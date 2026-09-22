open Rabbit_proverif_pv_parse.Pitptree

let node (desc, _, _) = desc

let () =
  let env, decls = Typer.load (Env.init_env ()) Sys.argv.(1) in
  let decls, _, _ = Proverif_compiler.compile_program env decls in
  let gets = ref 0 and tuples = ref 0 in
  let rec pattern = function
    | PPatTuple ps -> incr tuples; List.iter pattern ps
    | PPatFunApp (_, ps) -> List.iter pattern ps
    | PPatChoice _ -> failwith "Unexpected choice pattern"
    | PPatVar _ | PPatEqual _ | PPatAny _ -> ()
  in
  let rec visit process =
    match node process with
    | PGet (("persistent_fact_table", _), ps, cond, yes, no, _) ->
        incr gets;
        List.iter pattern ps;
        if Option.is_none cond then failwith "Payload constraints must be inside get";
        (match node yes with
         | PTest _ | PLet _ -> failwith "Payload matching must not follow row selection"
         | _ -> ());
        visit yes; visit no
    | PPar (a, b) | PTest (_, a, b) | PLet (_, _, a, b)
    | PLetFilter (_, _, a, b, _) | PGet (_, _, _, a, b, _) -> visit a; visit b
    | PRestr (_, _, _, p) | PRepl p | PInput (_, _, p, _) | POutput (_, _, p)
    | PEvent (_, _, _, p) | PPhase (_, p) | PBarrier (_, _, p)
    | PInsert (_, _, p) -> visit p
    | PNil | PLetDef _ -> ()
  in
  List.iter (function TPDef (_, _, p) -> visit p | _ -> ()) decls;
  if !gets <> 7 then failwith "Missing persistent guards";
  if !tuples <> 1 then failwith "Tuple decomposition must be in the get pattern"
