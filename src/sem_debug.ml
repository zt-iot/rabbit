open Sem

module V = struct
  type t = Subst.proc_id * Index.t
  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
end

module E = struct
  type t = edge
  let compare = compare
  let default =
    { id = Sem.edge_id @@ Ident.global "dummy"
    ; source = Index.zero
    ; source_env = Env.empty ()
    ; source_vars = []
    ; pre = []
    ; update = { rho= Ident.local "rho"
               ; register = Typed.{ env= Env.empty (); loc= Location.nowhere; desc= Unit }
               ; items= [] }
    ; tag = []
    ; post = []
    ; target = Index.zero
    ; target_env = Env.empty ()
    ; target_vars = []
    ; loop_back = false
    }
end
module G = Graph.Persistent.Digraph.ConcreteLabeled(V)(E)

(* XXX hack *)
let graph_attribute = ref []

let escape s = Printf.sprintf "%S" s

module G' = struct
    include G
    let graph_attributes _g = !graph_attribute (* XXX hack *)
    let default_vertex_attributes _g = []
    let vertex_name (proc_id,v) =
      escape
      @@ Ident.to_string (proc_id : Subst.proc_id :> Ident.t) ^ "_" ^ Index.to_string v
    let vertex_attributes _v = []
    let get_subgraph _v = None
    let default_edge_attributes _g = []

    let edge_label (t : Sem.edge) =
      String.escaped
      @@ String.concat ";\n"
      @@ Ident.to_string (t.id :> Ident.t)
         :: ("PRE:"^String.concat "; " (List.map string_of_fact t.pre))
         :: Update.to_string t.update
         :: (match t.tag with
             | [] -> []
             | fs -> [ "Tag:"
                       ^ String.concat "," (List.map string_of_fact fs)])
         @ ["POST:"^String.concat "; " (List.map string_of_fact t.post)]

    let edge_attributes (_,t,_) =
      [`Label (edge_label t) ]
      @ if t.loop_back then [ `Style `Dashed ] else []
end

module Viz = Graph.Graphviz.Dot(G')

let viz_of_models ms =
  List.fold_left (fun viz m ->
      List.fold_left (fun viz e ->
          G'.add_edge_e viz ((m.id, e.source), e, (m.id, e.target))) viz m.edges) G'.empty ms

let write_models_svg fn_svg ms =
  let fn_viz = fn_svg ^ ".viz" in
  let () =
    Out_channel.with_open_text fn_viz @@ fun oc ->
    Viz.output_graph oc @@ viz_of_models ms
  in
  ignore @@ Utils.runf "dot -Tsvg \"%s\" -o \"%s\"" fn_viz fn_svg
