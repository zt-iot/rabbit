open Sem

module V = struct
  type t = Ident.t * Index.t
  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
end

module E = struct
  type t = edge
  let compare = compare
  let default =
    { id = Ident.global "dummy"
    ; source = Index.zero
    ; source_env = Env.empty ()
    ; pre = []
    ; update = { register = None; mutable_overrides= []; drops= [] }
    ; tag = []
    ; post = []
    ; target = Index.zero
    ; target_env = Env.empty ()
    }
end
module G = Graph.Persistent.Digraph.ConcreteLabeled(V)(E)

(* XXX hack *)
let graph_attribute = ref []

module G' = struct
    include G
    let graph_attributes _g = !graph_attribute (* XXX hack *)
    let default_vertex_attributes _g = []
    let vertex_name (_,v) = Index.to_string v
    let vertex_attributes _v = []
    let get_subgraph _v = None
    let default_edge_attributes _g = []

    let edge_label t =
      String.concat ";\n"
      @@ Ident.to_string t.id
         :: ("PRE:"^String.concat "; " (List.map string_of_fact t.pre))
         :: string_of_update t.update
         :: (match t.tag with
             | [] -> []
             | fs -> [ "Tag:"
                       ^ String.concat "," (List.map string_of_fact fs)])
         @ ["POST:"^String.concat "; " (List.map string_of_fact t.post)]

    let edge_attributes (_,t,_) = [`Label (edge_label t) ]
end

module Viz = Graph.Graphviz.Dot(G')

let viz_of_graphs gs =
  List.fold_left (fun viz (id, es) ->
      List.fold_left (fun viz e ->
          G'.add_edge_e viz ((id,e.source), e, (id,e.target))) viz es) G'.empty gs

let write_graphs_svg fn_svg gs =
  let fn_viz = fn_svg ^ ".viz" in
  let () =
    Out_channel.with_open_text fn_viz @@ fun oc ->
    Viz.output_graph oc @@ viz_of_graphs gs
  in
  ignore @@ Utils.runf "dot -Tsvg \"%s\" -o \"%s\"" fn_viz fn_svg

(*
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

*)

(*
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

let write_tamarin_svg fn t =
  write_tamarin_graph (fn ^ ".viz") t;
  ignore @@ runf "dot -Tsvg \"%s\" -o \"%s\"" (fn ^ ".viz") fn
*)
