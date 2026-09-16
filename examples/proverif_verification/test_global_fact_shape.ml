open Rabbit_proverif_pv_parse.Pitptree

let check condition message = if not condition then failwith message
let node (desc, _, _) = desc
let has_option name options = List.exists (fun ((id, _), _) -> id = name) options

let inspect filename =
  let env, decls = Typer.load (Env.init_env ()) filename in
  let decls, top, _ = Proverif_compiler.compile_program env decls in
  let channels = List.filter_map (function
      | TFree (id, ("channel", _), options) when has_option "private" options -> Some id
      | _ -> None) decls in
  let channel = match channels with
    | [id] -> id
    | _ -> failwith "Expected exactly one shared private global-fact channel" in
  let symbols = List.filter_map (function
      | TFunDecl (((name, _) as id), _, _, options)
        when String.ends_with ~suffix:"__global_fact" name ->
          check (has_option "data" options) "Fact constructors must support patterns";
          Some id
      | _ -> None) decls in
  check (symbols <> []) "Missing global fact constructors";
  let outputs = ref [] and inputs = ref [] in
  let rec visit process =
    match node process with
    | POutput (ch, payload, rest) when node ch = PPIdent channel ->
        check (node rest = PNil) "Global output must not block the continuation";
        (match node payload with
         | PPFunApp (symbol, _) -> outputs := fst symbol :: !outputs
         | _ -> failwith "Missing fact constructor on output")
    | PInput (ch, PPatFunApp (symbol, _), rest, options)
      when node ch = PPIdent channel ->
        check (List.mem symbol symbols) "Unknown input constructor";
        check (has_option "precise" options) "Missing precise consumption annotation";
        inputs := fst symbol :: !inputs;
        visit rest
    | PPar (a, b) | PTest (_, a, b) | PLet (_, _, a, b)
    | PLetFilter (_, _, a, b, _) | PGet (_, _, _, a, b, _) -> visit a; visit b
    | PRepl p ->
        (* Replication in the system may instantiate consumers, but the linear
           fixture must not replicate a pending fact or its command body. *)
        check (Filename.basename filename <> "global_facts_linear.rab")
          "Unexpected replication in the single-use fixture";
        visit p
    | PRestr (id, _, _, p) ->
        check (id <> channel) "The shared channel was restricted inside a process";
        visit p
    | PInput (_, _, p, _) | POutput (_, _, p) | PEvent (_, _, _, p)
    | PPhase (_, p) | PBarrier (_, _, p) | PInsert (_, _, p) -> visit p
    | PNil | PLetDef _ -> ()
  in
  List.iter (function TPDef (_, _, p) -> visit p | _ -> ()) decls;
  visit top;
  if Filename.basename filename = "global_facts_linear.rab" then (
    let count name xs = List.length (List.filter ((=) name) xs) in
    check (count "Once__global_fact" !outputs = 1) "Single-use fact was duplicated";
    check (count "Once__global_fact" !inputs = 2) "Repeated guard lost an input";
    check (count "Twice__global_fact" !outputs = 2) "Equal outputs were deduplicated";
    check (count "Twice__global_fact" !inputs = 2) "Two-fact guard lost an input")

let () = Array.iteri (fun i filename -> if i > 0 then inspect filename) Sys.argv
