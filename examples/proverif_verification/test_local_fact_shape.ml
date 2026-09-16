open Rabbit_proverif_pv_parse.Pitptree

let check condition message = if not condition then failwith message
let node (desc, _, _) = desc
let has_option name options = List.exists (fun ((id, _), _) -> id = name) options
let local_symbol (name, _) = String.ends_with ~suffix:"__local_fact" name
let local_channel (name, _) = String.starts_with ~prefix:"local_fact_ch" name

let inspect filename =
  let env, decls = Typer.load (Env.init_env ()) filename in
  let decls, top, _ = Proverif_compiler.compile_program env decls in
  let restricted = ref [] and outputs = ref [] and inputs = ref [] in
  let rec visit owner process =
    match node process with
    | PRestr (id, _, _, p) ->
        check (not (local_channel id)) "Local channel must be restricted at process entry";
        visit owner p
    | POutput (ch, payload, rest) ->
        (match node payload with
         | PPFunApp (symbol, _) when local_symbol symbol ->
             check (Option.map (fun id -> PPIdent id) owner = Some (node ch))
               "Output escaped its process-local channel";
             check (node rest = PNil) "Local output blocks its continuation";
             outputs := fst symbol :: !outputs
         | _ -> ());
        visit owner rest
    | PInput (ch, pattern, rest, options) ->
        (match pattern with
         | PPatFunApp (symbol, _) when local_symbol symbol ->
             check (Option.map (fun id -> PPIdent id) owner = Some (node ch))
               "Input escaped its process-local channel";
             check (has_option "precise" options) "Missing precise consumption annotation";
             inputs := fst symbol :: !inputs
         | _ -> ());
        visit owner rest
    | PPar (a, b) | PTest (_, a, b) | PLet (_, _, a, b)
    | PLetFilter (_, _, a, b, _) | PGet (_, _, _, a, b, _) ->
        visit owner a; visit owner b
    | PRepl p ->
        check (Filename.basename filename <> "local_facts_linear.rab")
          "Unexpected replication of the linear fixture";
        visit owner p
    | PEvent (_, _, _, p) | PPhase (_, p) | PBarrier (_, _, p)
    | PInsert (_, _, p) -> visit owner p
    | PNil | PLetDef _ -> ()
  in
  List.iter (function
      | TFree (id, _, _) -> check (not (local_channel id)) "Local store declared globally"
      | TFunDecl (id, _, _, options) when local_symbol id ->
          check (has_option "data" options) "Local constructor cannot be matched"
      | TPDef (_, _, p) ->
          (match node p with
           | PRestr (id, _, ("channel", _), body) when local_channel id ->
               check (not (List.mem id !restricted)) "Separate definitions share a binder";
               restricted := id :: !restricted;
               visit (Some id) body
           | _ -> visit None p)
      | _ -> ()) decls;
  visit None top;
  let expected = if Filename.basename filename = "local_facts_isolation.rab" then 4 else 1 in
  check (List.length !restricted = expected) "Wrong number of process-entry restrictions";
  if Filename.basename filename = "local_facts_linear.rab" then (
    let count name xs = List.length (List.filter ((=) name) xs) in
    check (count "Once__local_fact" !outputs = 1) "Single-use fact duplicated";
    check (count "Once__local_fact" !inputs = 2) "Repeated guard lost an input";
    check (count "Twice__local_fact" !outputs = 2) "Equal occurrences deduplicated";
    check (count "Twice__local_fact" !inputs = 2) "Two-fact guard lost an input")

let () = Array.iteri (fun i filename -> if i > 0 then inspect filename) Sys.argv
