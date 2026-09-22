open Rabbit_proverif_pv_parse.Pitptree

let check condition message = if not condition then failwith message
let node (desc, _, _) = desc
let local_wrapper (name, _) = name = "persistent_local_fact"
let global_table (name, _) = name = "persistent_fact_table"
let local_id (name, _) = String.starts_with ~prefix:"local_fact_id" name

let () =
  let env, decls = Typer.load (Env.init_env ()) Sys.argv.(1) in
  let decls, top, _ = Proverif_compiler.compile_program env decls in
  let owners = ref [] and inserts = ref 0 and gets = ref 0 in
  let global_inserts = ref 0 and global_gets = ref 0 in
  let rec visit owner process =
    match node process with
    | PRestr (id, _, _, rest) ->
        check (not (local_id id)) "Identity must be restricted at process entry";
        visit owner rest
    | PInsert (table, args, rest) ->
        check (global_table table) "Persistent facts must use the shared table";
        (match List.map node args with
         | [PPFunApp (wrapper, [key; _])] when local_wrapper wrapper ->
             incr inserts;
             check (Some (node key) = Option.map (fun id -> PPIdent id) owner)
               "Insert must use its invocation identity"
         | [PPFunApp ((name, _), _)] when String.ends_with ~suffix:"__global_fact" name ->
             incr global_inserts
         | _ -> failwith "Unexpected persistent payload");
        visit owner rest
    | PGet (table, patterns, _, yes, no, _) ->
        check (global_table table) "Persistent facts must use the shared table";
        (match patterns with
         | [PPatFunApp (wrapper, [PPatEqual key; _])] when local_wrapper wrapper ->
             incr gets;
             check (Some (node key) = Option.map (fun id -> PPIdent id) owner)
               "Get must match its invocation identity"
         | [PPatFunApp ((name, _), _)] when String.ends_with ~suffix:"__global_fact" name ->
             incr global_gets
         | _ -> failwith "Unexpected persistent pattern");
        visit owner yes; visit owner no
    | PPar (a, b) | PTest (_, a, b) | PLet (_, _, a, b)
    | PLetFilter (_, _, a, b, _) -> visit owner a; visit owner b
    | PRepl p | PInput (_, _, p, _) | POutput (_, _, p)
    | PEvent (_, _, _, p) | PPhase (_, p) | PBarrier (_, _, p) -> visit owner p
    | PNil | PLetDef _ -> ()
  in
  check (List.exists (function
      | TFunDecl (id, [("bitstring", _); ("bitstring", _)], ("bitstring", _), options) ->
          local_wrapper id && List.exists (fun ((name, _), _) -> name = "data") options
      | _ -> false) decls) "Missing data constructor for invocation-local payloads";
  List.iter (function
      | TTableDecl (("persistent_local_fact_table", _), _) ->
          failwith "Separate persistent local table must not be declared"
      | TFree (id, _, _) -> check (not (local_id id)) "Identity must not be global"
      | TPDef (_, _, p) ->
          (match node p with
           | PRestr (id, _, ("bitstring", _), body) when local_id id ->
               check (not (List.mem id !owners)) "Definitions share an identity binder";
               owners := id :: !owners;
               visit (Some id) body
           | _ -> visit None p)
      | _ -> ()) decls;
  visit None top;
  check (List.length !owners = 2) "Writer and reader need invocation-local identities";
  check (!inserts = 2 && !gets = 3) "Missing local accesses in main or nested calls";
  check (!global_inserts = 1 && !global_gets = 1) "Missing global accesses"
