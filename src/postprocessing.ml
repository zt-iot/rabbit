(* optimize models.contents
    For each process fact, we determine, over-approximately, whether the fact is
    boolean. A fact is boolean if there cannot be more than one instance of it at each 
    fact environment. Ie., then A(x) is generated, it has to be consumed somehow before
    A(y) happens. 
*)

(* given a model and an identifier of a local fact, 
  determine if it is boolean  *)
(* let is_boolean (m : Totamarin.model) (f : string)  *)
  type ('a, 'b) sum = 
  | Inl of 'a  (* Left injection *)
  | Inr of 'b  (* Right injection *)

open Totamarin

let rec state_eq_ind (i : ((int list) * int) list) j = 
  match i, j with
  | (il, x) :: i, (jl, y) :: j -> il = jl && x = y && state_eq_ind i j
  | [], [] -> true
  | _, _ -> false

let state_eq st1 st2 = 
  state_eq_ind st1.state_index st2.state_index

let forward_transitions_from (m : model) (st : state) : transition list = 
  List.filter (fun (tr : transition) -> state_index_to_string_aux st = state_index_to_string_aux tr.transition_from && not tr.transition_is_loop_back) m.model_transitions

let forward_transitions_to (m : model) (st : state) : transition list = 
  List.filter (fun (tr : transition) -> state_index_to_string_aux st = state_index_to_string_aux tr.transition_to && not tr.transition_is_loop_back) m.model_transitions
  

let is_nonlocal_fact f = 
  match f with
  | ChannelFact _ -> true
  | GlobalFact _ -> true
  | _ -> false

(* preprocess the model so variables in different transitions are unique.is_persist
  We do this to make merging transitoins easier. Otherwise, we must consider variable conflict each time 
  we do merging.. 
*)

let rec expr_unify_vars e =
  match e with 
  | MetaVar i -> Var ("meta"^ !separator ^string_of_int i)
  | LocVar i -> Var ("loc"^ !separator ^string_of_int i)
  | TopVar i -> Var ("top"^ !separator ^string_of_int i)
  | MetaNewVar i -> Var ("new"^ !separator ^string_of_int i)
  | Apply (f, el) -> Apply (f, List.map expr_unify_vars el)
  | List el -> List (List.map expr_unify_vars el)
  | AddOne e -> AddOne (expr_unify_vars e)
  | _ -> e

let fact_rec_on_expr f (p : expr -> expr) = 
  match f with
  | Fact (fid, nsp, el) -> Fact (fid, nsp, List.map p el)
  | ConstantFact (e1, e2) -> ConstantFact (p e1, p e2)
  | GlobalFact (fid, el) -> GlobalFact (fid, List.map p el)
  | ChannelFact (fid, ch, el) -> ChannelFact (fid, p ch, List.map p el)
  | PathFact (fid, nsp, path, el) ->  PathFact (fid, nsp, p path, List.map p el)
  | ResFact (n, el) -> ResFact (n, List.map p el)
  | AccessFact (nsp, ch, sys) -> AccessFact (nsp, p ch, sys)
  | FileFact (nsp, path, data) -> FileFact(nsp, path, p data)
  | InitFact el -> InitFact (List.map p el)
  | _ -> error ~loc:Location.Nowhere (UnintendedError "process fact isnt there")

let fact_unify_vars f =
  fact_rec_on_expr f expr_unify_vars

let rec expr_expand_var e ind = 
  match e with
  | Var v -> Var (v ^ !separator ^ string_of_int ind)
  | Apply (f, el) -> Apply (f, List.map (fun e -> expr_expand_var e ind) el)
  | List el -> List (List.map (fun e -> expr_expand_var e ind) el)
  | AddOne e -> AddOne (expr_expand_var e ind)
  | MetaVar i | LocVar i | TopVar i -> error ~loc:Location.Nowhere (UnintendedError "variables should have been unified")
  | _ -> e

  let fact_expand_var f ind =
    fact_rec_on_expr f (fun e -> expr_expand_var e ind)


let rec expr_subst_var e1 s e2 = 
match e1 with
| Var v -> (if s = v then e2 else e1)
| Apply (f, el) -> Apply (f, List.map (fun e -> expr_subst_var e s e2) el)
| List el -> List (List.map (fun e -> expr_subst_var e s e2) el)
| AddOne e -> AddOne (expr_subst_var e s e2)
| MetaVar i | LocVar i | TopVar i -> error ~loc:Location.Nowhere (UnintendedError "variables should have been unified")
| _ -> e1

let fact_subst_var f s e =
  fact_rec_on_expr f (fun e' -> expr_subst_var e' s e)

let rec expr_subst_vars e1 substs = 
  match substs with
  | (s, e) :: substs -> expr_subst_vars (expr_subst_var e1 s e) substs
  | [] -> e1

let fact_subst_vars f substs =
  fact_rec_on_expr f (fun e' -> expr_subst_vars e' substs)
  

let unify_then_expand_variables (tr : transition) (i : int) =
  let p = fun f -> fact_expand_var (fact_unify_vars f) i  in
  let q = fun f -> expr_expand_var (expr_unify_vars f) i  in
  {tr with 
    transition_pre = List.map p tr.transition_pre;
    transition_post = List.map p tr.transition_post;
    transition_state_transition = 
    let (a, b, c, d), (e, f, g, h) = tr.transition_state_transition in
    (q a, List.map q b, List.map q c, List.map q d), 
    (q e, List.map q f, List.map q g, List.map q h)
  }

let model_remove_transition_by_id (m : model) id =
  {m with 
    model_transitions = List.filter (fun tr -> tr.transition_id <> id) m.model_transitions
  }

let make_variables_unique (m : model) = 
  {
    m with model_transitions=
      List.map (fun tr -> unify_then_expand_variables tr tr.transition_id) m.model_transitions 
  }

(* p *)
let rec optimize_at (m : model) (st : state) =

  let tr1_lst = forward_transitions_from m st in
  print_endline (string_of_int (List.length tr1_lst));
  print_endline (state_index_to_string_aux st);

  let m = List.fold_left (fun m tr -> optimize_at m tr.transition_to) m tr1_lst in 

  let m = List.fold_left (fun m tr1 ->
    let st_m = tr1.transition_to in 
    let tr2_lst = forward_transitions_from m st_m in
    let m = List.fold_left (fun m (tr2 : transition) -> 
      let st_f = tr2.transition_to in 
      (* judge if we will merge these edges st -[tr1]-> st_m -> [tr2] -> st_f  *)
      let label = 
        begin match tr1.transition_label, tr2.transition_label with
        | [], l -> Some (Inr tr2.transition_label)
        | l, [] -> Some (Inl tr1.transition_label)
        | _, _ -> None
      end in
      let nonlocal = List.exists (fun a -> is_nonlocal_fact a) tr2.transition_pre in
      let out_num = List.length (forward_transitions_from m st_m) in
      let in_num = List.length (forward_transitions_to m st_m) in
      let inout = out_num > 1 && in_num > 1 in
      (* if label = None, dont merge *)
      match label, nonlocal, inout with
      | Some label, false, false ->


        print_endline "Merging";
        print_endline ("- " ^ print_transition tr1 true);
        print_endline ("- " ^ print_transition tr2 true);

        begin
          let m = (if out_num ==1 then model_remove_transition_by_id m tr1.transition_id else m) in 
          let m = (if in_num == 1 then model_remove_transition_by_id m tr2.transition_id else m) in 
          let (ret1, meta1, loc1, top1) = (snd tr1.transition_state_transition) in
          let (ret2, meta2, loc2, top2) = (fst tr2.transition_state_transition) in
          let substs = List.map2 (fun f t -> 
            match f with
            | Var s -> (s, t)
            | _ -> error ~loc:Location.Nowhere (UnintendedError "from is not a variable")            
            ) (ret2 :: meta2 @ loc2 @ top2) (ret1 :: meta1 @ loc1 @ top1) in
            let (ret, meta, loc, top) = (snd tr2.transition_state_transition) in
            let pre2' = List.map (fun f -> fact_subst_vars f substs) tr2.transition_pre in 
            let post2 = List.map (fun f -> fact_subst_vars f substs) tr2.transition_post in 
            let pre2 = List.fold_left 
              (fun pre2 f -> 
                match f with
                | Fact (fid, _, el) ->
                  print_endline ("processing: "^ fid);
                  begin match List.find_opt 
                    (fun f -> 
                      match f with 
                      | Fact (fid', _, el') ->  
                        print_endline ("comparing : "^ fid');
                        fid = fid'
                      | _ -> false) tr1.transition_post with
                  | None -> f::pre2
                  | Some f' -> 
                    begin match f' with
                    | Fact (_, _,el') -> 
                      pre2 @ (List.map2 (fun e e' -> ResFact(0, [e; e'])) el el')
                    | _ -> error ~loc:Location.Nowhere (UnintendedError "")
                    end
                  end
                | f -> f::pre2) [] pre2' in 
            let post1 = List.filter (fun f ->
              begin match f with
              | Fact (fid, _, _) ->
                not (List.exists (fun f -> match f with | Fact(fid', _, _) -> fid = fid' | _ -> false) pre2')
              | _ -> true end) tr1.transition_post in 
          add_transition m {
            transition_id = m.model_transition_id_max;
            transition_namespace = m.model_name;
            transition_name = "merged";
            transition_from = st;
            transition_to = st_f;
            transition_pre = tr1.transition_pre @ pre2;
            transition_post = post1 @ post2;
            transition_state_transition = 
              fst tr1.transition_state_transition, 
                (expr_subst_vars ret substs, 
                List.map (fun e -> expr_subst_vars e substs) meta,
                List.map (fun e -> expr_subst_vars e substs) loc,
                List.map (fun e -> expr_subst_vars e substs) top);
            transition_label = 
              (match label with
              | Inl label -> 
                label
              | Inr label ->
                List.map (fun f -> fact_subst_vars f substs) label)
            ;
            transition_is_loop_back = false       
          }        
        end 
      | _ -> 
        m
    ) m tr2_lst in m) m tr1_lst in
  m 

let optimize (m : model) =
let m = make_variables_unique m in 
  optimize_at m (m.model_init_state)
