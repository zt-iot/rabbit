open Tamarin

module V = struct
  type t = state
  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
end
module E = struct
  type t = transition
  let compare = compare
  let default =
    { transition_id = -1
    ; transition_namespace = "Invalid"
    ; transition_name = "Invalid"
    ; transition_from = { state_namespace = "Invalid"; state_index= Mindex.zero; state_vars = { meta= -1; loc= -1; top= -1 } }
    ; transition_to = { state_namespace = "Invalid"; state_index= Mindex.zero; state_vars = { meta= -1; loc= -1; top= -1 } }
    ; transition_pre = []
    ; transition_post = []
    ; transition_state_transition = empty_state_desc, empty_state_desc
    ; transition_label = []
    ; transition_is_loop_back = false
    }
end
module G = Graph.Persistent.Digraph.ConcreteLabeled(V)(E)

(* XXX hack *)
let graph_attribute = ref []

module G' = struct
    include G
    let graph_attributes _g = !graph_attribute (* XXX hack *)
    let default_vertex_attributes _g = []
    let vertex_name v = Mindex.to_string v.state_index
    let vertex_attributes _v = []
    let get_subgraph _v = None
    let default_edge_attributes _g = []

    let state_desc sd =
      String.concat "; "
        (List.map print_expr (sd.ret :: sd.metas @ sd.locs @ sd.tops))

    let edge_label t =
      String.concat ";\n"
      @@ t.transition_name
         :: ("PRE:"^String.concat "; " (List.map string_of_fact t.transition_pre))
         :: (state_desc (fst t.transition_state_transition)
             ^ " => "
             ^ state_desc (snd t.transition_state_transition))
         :: (match t.transition_label with
             | [] -> []
             | fs -> [ "Event:"
                       ^ String.concat "," (List.map string_of_fact fs)])
         @ ["POST:"^String.concat "; " (List.map string_of_fact t.transition_post)]

    let edge_attributes (_,t,_) = [`Label (edge_label t) ]
end

module Viz = Graph.Graphviz.Dot(G')

let add_model g (m : model) =
  List.fold_left (fun g t ->
      let from = t.transition_from in
      let to_ = t.transition_to in
      G'.add_edge_e g (from, t, to_)) g m.model_transitions

let write_graph fn g =
  Out_channel.with_open_text fn @@ fun oc ->
  Viz.output_graph oc g

let write_tamarin_graph fn t =
  let g = List.fold_left add_model G'.empty t.models in
  graph_attribute := [`Label (String.concat ";\n"
                                (List.filter_map (function
                                     | Comment _ -> None
                                     | Rule {name; role; pre; label; post} ->
                                         Some (Printf.sprintf "%s (%s) pre:(%s) label:(%s) post:(%s)" name role
                                                 (String.concat ";" (List.map string_of_fact pre))
                                                 (String.concat ";" (List.map string_of_fact label))
                                                 (String.concat ";" (List.map string_of_fact post))
                                              ))
                                 t.rules)) ];
  write_graph fn g

let run (com : string) : int * string list =
  Format.printf "execute %s@." com;
  let ic = Unix.open_process_in com in
  let outputs = In_channel.input_lines ic in
  let exit =
    match Unix.close_process_in ic with
    | WEXITED n -> n
    | _ -> assert false
  in
  exit, outputs

let runf fmt = Printf.ksprintf run fmt

let write_tamarin_svg fn t =
  write_tamarin_graph (fn ^ ".viz") t;
  ignore @@ runf "dot -Tsvg \"%s\" -o \"%s\"" (fn ^ ".viz") fn
