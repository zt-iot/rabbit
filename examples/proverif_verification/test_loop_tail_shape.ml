open Rabbit_proverif_pv_parse.Pitptree

let node (desc, _, _) = desc
let check condition message = if not condition then failwith message
let named prefix (name, _) = String.starts_with ~prefix name
let channel_is id ch = node ch = PPIdent id

let children process = match node process with
  | PPar (a, b) | PTest (_, a, b) | PLet (_, _, a, b)
  | PLetFilter (_, _, a, b, _) | PGet (_, _, _, a, b, _) -> [a; b]
  | PRepl p | PRestr (_, _, _, p) | PInput (_, _, p, _)
  | POutput (_, _, p) | PEvent (_, _, _, p) | PPhase (_, p)
  | PBarrier (_, _, p) | PInsert (_, _, p) -> [p]
  | PNil | PLetDef _ -> []

let rec fold f acc process =
  List.fold_left (fold f) (f acc process) (children process)

let done_message payload = match node payload with
  | PPTuple (flag :: _) -> (match node flag with PPIdent ("true__bool", _) -> true | _ -> false)
  | _ -> false

let done_pattern = function
  | PPatTuple (PPatEqual flag :: _) ->
      (match node flag with PPIdent ("true__bool", _) -> true | _ -> false)
  | _ -> false

let inspect filename =
  let env, decls = Typer.load (Env.init_env ()) filename in
  let decls, top, _ = Proverif_compiler.compile_program env decls in
  let counts = Hashtbl.create 8 in
  let count name = Hashtbl.replace counts name (1 + Option.value ~default:0 (Hashtbl.find_opt counts name)) in
  let inspect_choice id body =
    let rec parallel_parts process = match node process with
      | PPar (a, b) -> parallel_parts a @ parallel_parts b
      | _ -> [process]
    in
    let initial_tokens = List.filter (fun process -> match node process with
      | POutput (ch, _, _) -> channel_is id ch
      | _ -> false) (parallel_parts body) in
    check (List.length initial_tokens = 1) "Choice must start with exactly one token";
    let choice_inputs = fold (fun n process -> match node process with
      | PInput (ch, pattern, _, _) when channel_is id ch && not (done_pattern pattern) -> n + 1
      | _ -> n) 0 body in
    check (choice_inputs = 2) "Both branches must compete for the same choice token";
    let inputs, outputs = fold (fun (inputs, outputs) process -> match node process with
      | PInput (ch, pattern, _, _) when channel_is id ch && done_pattern pattern -> inputs + 1, outputs
      | POutput (ch, payload, _) when channel_is id ch && done_message payload -> inputs, outputs + 1
      | _ -> inputs, outputs) (0, 0) body in
    if inputs = 0 then (
      count "tail_case";
      check (outputs = 0) "Tail case still emits an unused completion token";
      let releases = fold (fun n process -> match node process with
        | POutput (ch, _, _) ->
            (match node ch with PPIdent id when named "loop_ch__" id -> n + 1 | _ -> n)
        | _ -> n) 0 body in
      check (releases = 2) "Each of the two tail branches must release the loop exactly once")
    else (
      count "ordinary_case";
      check (inputs = 1 && outputs = 2) "Non-tail case must retain its shared continuation")
  in
  let rec visit parent process =
    (match node process with
     | PRestr (id, _, _, body) when named "case_ch__" id || named "channel_case_ch__" id ->
         inspect_choice id body
     | POutput (_, payload, rest) ->
         (match node payload with
          | PPFunApp ((name, _), _) when String.starts_with ~prefix:"Tail" name ->
              count name;
              check (node rest = PNil) "Pending fact output unexpectedly has a continuation";
              (match Option.map node parent with
               | Some (POutput (ch, state, _)) ->
                   (match node ch with
                    | PPIdent id -> check (named "loop_ch__" id) "Expected the enclosing loop token"
                    | _ -> failwith "Unexpected loop channel term");
                   check (done_message state = (name = "TailUntil__chan"))
                     "Repeat/until token has the wrong completion flag"
               | _ -> failwith "Tail output must follow the internal loop output")
          | PPFunApp (("Ordinary__chan", _), _) ->
              count "ordinary_output";
              check (node rest = PNil) "Ordinary output must remain asynchronous";
              (match Option.map node parent with
               | Some (PPar _) -> ()
               | _ -> failwith "A non-tail output was reordered")
          | _ -> ())
     | _ -> ());
    List.iter (visit (Some process)) (children process)
  in
  List.iter (function TPDef (_, _, p) -> visit None p | _ -> ()) decls;
  visit None top;
  List.iter (fun (name, expected) ->
    let actual = Option.value ~default:0 (Hashtbl.find_opt counts name) in
    check (actual = expected) (Printf.sprintf "%s: expected %d, got %d" name expected actual))
    ["tail_case", 4; "ordinary_case", 1; "ordinary_output", 2;
     "TailGeneral__chan", 2; "TailShared__chan", 2;
     "TailUntil__chan", 1; "TailDenied__chan", 1]

let () = inspect Sys.argv.(1)
