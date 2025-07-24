open Tamarin

let debug = ref false

type error =
  | ConflictingCondition'

exception Error of error

(** [error err] raises the given runtime error. *)
let error' err = Stdlib.raise (Error err)

(** Print error description. *)
let print_error err ppf =
  match err with
  | ConflictingCondition' ->   Format.fprintf ppf "ConflictingCondition'"


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


let forward_transitions_from (m : model) (st : state) : transition list =
  List.filter (fun (tr : transition) -> state_index_to_string_aux st = state_index_to_string_aux tr.transition_from && not tr.transition_is_loop_back) m.model_transitions

let _forward_transitions_to (m : model) (st : state) : transition list =
  List.filter (fun (tr : transition) -> state_index_to_string_aux st = state_index_to_string_aux tr.transition_to && not tr.transition_is_loop_back) m.model_transitions

let forward_transitions_from' (m : model) (st : state) : transition list =
  List.filter (fun (tr : transition) -> state_index_to_string_aux st = state_index_to_string_aux tr.transition_from) m.model_transitions

let forward_transitions_to' (m : model) (st : state) : transition list =
  List.filter (fun (tr : transition) -> state_index_to_string_aux st = state_index_to_string_aux tr.transition_to) m.model_transitions


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
  | MetaVar i -> Var ("m"^ !separator ^string_of_int i)
  | LocVar i -> Var ("l"^ !separator ^string_of_int i)
  | TopVar i -> Var ("t"^ !separator ^string_of_int i)
  | MetaNewVar i -> Var ("n"^ !separator ^string_of_int i)
  | Apply (f, el) -> Apply (f, List.map expr_unify_vars el)
  | List el -> List (List.map expr_unify_vars el)
  | AddOne e -> AddOne (expr_unify_vars e)
  | FVar e -> FVar (expr_unify_vars e)
  | _ -> e

let fact_rec_on_expr f (p : expr -> expr) =
  match f with
  | Fact (fid, nsp, el) -> Fact (fid, nsp, List.map p el)
  | ConstantFact (e1, e2) -> ConstantFact (p e1, p e2)
  | GlobalFact (fid, el) -> GlobalFact (fid, List.map p el)
  | ChannelFact (fid, ch, el) -> ChannelFact (fid, p ch, List.map p el)
  | PathFact (fid, nsp, path, el) ->  PathFact (fid, nsp, p path, List.map p el)
  | EqFact (e1, e2) -> EqFact (p e1, p e2)
  | NeqFact (e1, e2) -> NeqFact (p e1, p e2)
  | AccessFact (nsp, param, ch, sys) -> AccessFact (nsp,p param, p ch, sys)
  | AccessGenFact (nsp, param) -> AccessGenFact (nsp, p param)
  | FileFact (nsp, path, data) -> FileFact(nsp, path, p data)
  | InitFact el -> InitFact (List.map p el)
  | InjectiveFact (fid, nsp, e, el) -> InjectiveFact (fid, nsp, p e,  p el)
  | FreshFact e ->  FreshFact (p e)
  | FreshFact' e ->  FreshFact' (p e)
  | LoopFact _
  | AttackFact _  -> f
  | _ -> assert false

let fact_unify_vars f =
  fact_rec_on_expr f expr_unify_vars

let rec expr_expand_var e ind =
  match e with
  | Var v -> Var (v ^ !separator ^ string_of_int ind)
  | Apply (f, el) -> Apply (f, List.map (fun e -> expr_expand_var e ind) el)
  | List el -> List (List.map (fun e -> expr_expand_var e ind) el)
  | AddOne e -> AddOne (expr_expand_var e ind)
  | FVar e -> FVar (expr_expand_var e ind)
  | MetaVar _i | LocVar _i | TopVar _i -> assert false
  | _ -> e

let fact_expand_var f ind =
  fact_rec_on_expr f (fun e -> expr_expand_var e ind)


let rec expr_subst_var e1 s e2 =
match e1 with
| Var v -> (if s = v then e2 else e1)
| Apply (f, el) -> Apply (f, List.map (fun e -> expr_subst_var e s e2) el)
| List el -> List (List.map (fun e -> expr_subst_var e s e2) el)
| AddOne e -> AddOne (expr_subst_var e s e2)
| FVar e -> FVar (expr_subst_var e s e2)
| MetaVar _i | LocVar _i | TopVar _i -> assert false
| _ -> e1

(* xxx unused *)
let _fact_subst_var f s e =
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
    transition_label = List.map p tr.transition_label;
    transition_state_transition =
      let x, y = tr.transition_state_transition in
      (map_state_desc q x, map_state_desc q y)
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

(* given the postcondition of the first transition and the precondition of the second of
  some consecutive transitions, assumign the second, already variabes are substituted,
  give new pre and post conditions. If failed, return None
  *)


let fact_eq_by_fid f fid' =
  begin match f with
  | Fact (fid, _, _) -> fid = fid'
  | GlobalFact (fid, _) -> fid = fid'
  | ChannelFact (fid, _, _) -> fid = fid'
  | PathFact (fid, _, _, _) -> fid = fid'
  | InjectiveFact (fid, _,_, _) -> fid = fid'
  | _ -> false
  end

let fact_eq_file_fact f =
  begin match f with
  | FileFact (_, _, _) -> true
  | _ -> false
  end

(*
  given f : [...] -> post and g : pre' --> [...]
  optionally give new pair of pre and post.
  pre', expressions are already substituted
*)
let reduce_conditions post pre' =
  begin try
    let pre = List.fold_left
    (fun pre f ->
      match f with
      | Fact (fid, _, _)
      | PathFact (fid, _, _, _) ->
        begin match List.filter (fun f -> fact_eq_by_fid f fid) post with
        | [] -> f :: pre
        | _ -> error' ConflictingCondition'
        end
      | InjectiveFact (fid, _, e', arg') ->
        begin match List.filter (fun f -> fact_eq_by_fid f fid) post with
        | [] -> f :: pre
        | [InjectiveFact (_, _, e, arg)] ->
          if !debug then (
            print_endline "Testing";
            print_endline ("- " ^ Tamarin.print_expr e);
            print_endline ("- " ^ Tamarin.print_expr e');
          );

          if e = e'
          then (
            if !debug then print_endline ("- judged equal");
            (EqFact (arg, arg'))::pre
          ) else (
            if !debug then print_endline ("- judged inequal");
            error' ConflictingCondition'
          )
        | _ -> error' ConflictingCondition'
        end
      | FileFact (_, _, _) ->
        begin match List.filter (fun f -> fact_eq_file_fact f) post with
        | [] -> f :: pre
        | _ -> error' ConflictingCondition'
        end
      | _ -> f :: pre) [] pre' in

      let post = List.filter
      (fun f ->
        begin match f with
        | Fact (fid, _, _) | PathFact (fid, _, _, _) | InjectiveFact (fid, _, _, _) -> not (List.exists (fun f -> fact_eq_by_fid f fid) pre')
        | FileFact (_, _, _) -> not (List.exists (fun f -> fact_eq_file_fact f) pre')
        | _ -> true end) post in
      Some (post, pre)
  with
  | Error ConflictingCondition' -> None
  end

(* p *)
let rec optimize_at (m : model) (st : state) =

  let tr1_lst = forward_transitions_from m st in
  (* print_endline (string_of_int (List.length tr1_lst));
  print_endline (state_index_to_string_aux st); *)

  let m = List.fold_left (fun m tr -> optimize_at m tr.transition_to) m tr1_lst in

  let m = List.fold_left (fun m tr1 ->
    let st_m = tr1.transition_to in
    let tr2_lst = forward_transitions_from m st_m in
    let m = List.fold_left (fun m (tr2 : transition) ->
      let st_f = tr2.transition_to in
      (* judge if we will merge these edges st -[tr1]-> st_m -> [tr2] -> st_f  *)
      let is_labelled =
        begin match tr1.transition_label, tr2.transition_label with
        | [], [] -> Some (Inl [])
        | l, [] ->
          begin
          (* when only tr1 has a label, merge when tr2 is local *)
            if
              List.length tr2.transition_pre  > 0
            (* List.exists (fun a -> is_nonlocal_fact a) tr2.transition_pre  *)
            || List.exists (fun a -> is_nonlocal_fact a) tr2.transition_post then
              None
            else Some (Inl l)
          end
        | [], l ->
          begin
            (* when only tr2 has a label, merge when tr1's post is local *)
              if List.exists (fun a -> is_nonlocal_fact a) tr1.transition_post then
                None
              else Some (Inr l)
            end
        | _, _ -> None
      end in
      let nonlocal = List.exists (fun a -> is_nonlocal_fact a) tr2.transition_pre in
      let out_num = List.length (forward_transitions_from' m st_m) in
      let in_num = List.length (forward_transitions_to' m st_m) in
      let inout = out_num > 1 && in_num > 1 in
      (* if label = None, dont merge *)
      match is_labelled, nonlocal, inout with
      | Some la, false, false ->

        if !debug then (
          print_endline "Merging";
          print_endline ("- " ^ print_transition tr1 ~dev:true);
          print_endline ("- " ^ print_transition tr2 ~dev:true)
        );

        begin
          let {ret= ret1; metas= meta1; locs= loc1; tops= top1} = (snd tr1.transition_state_transition) in
          let {ret= ret2; metas= meta2; locs= loc2; tops= top2} = (fst tr2.transition_state_transition) in
          let substs = List.map2 (fun f t ->
            match f with
            | Var s -> (s, t)
            | _ -> assert false
            ) (ret2 :: meta2 @ loc2 @ top2) (ret1 :: meta1 @ loc1 @ top1) in
            let {ret= ret; metas= meta; locs= loc; tops= top} = (snd tr2.transition_state_transition) in
            let pre2 = List.map (fun f -> fact_subst_vars f substs) tr2.transition_pre in
            let post2 = List.map (fun f -> fact_subst_vars f substs) tr2.transition_post in
            let la =
              begin match la with
              | Inl la -> la
              | Inr la -> List.map (fun f -> fact_subst_vars f substs) la
              end in
            match reduce_conditions tr1.transition_post pre2 with
            | Some (post1, pre2) ->

              let m = (if out_num ==1 then model_remove_transition_by_id m tr1.transition_id else m) in
              let m = (if in_num == 1 then model_remove_transition_by_id m tr2.transition_id else m) in
              let tr = {
                transition_id = m.model_transition_id_max;
                transition_namespace = m.model_name;
                transition_name = tr1.transition_name ^ "_" ^ tr2.transition_name;
                transition_from = st;
                transition_to = st_f;
                transition_pre = tr1.transition_pre @ pre2;
                transition_post = post1 @ post2;
                transition_action =
                  (match tr1.transition_action, tr2.transition_action with
                   | None, _ | _, None -> None
                   | Some a1, Some a2 -> Some (a1 @ a2));
                transition_state_transition =
                  fst tr1.transition_state_transition,
                    { ret= expr_subst_vars ret substs;
                      metas= List.map (fun e -> expr_subst_vars e substs) meta;
                      locs= List.map (fun e -> expr_subst_vars e substs) loc;
                      tops= List.map (fun e -> expr_subst_vars e substs) top };
                transition_label = la;
                transition_is_loop_back = false
              } in
              if !debug then (
                print_endline "Merged into:";
                print_endline ("- " ^ print_transition tr ~dev:true)
              );
              add_transition m tr
            | _ ->
              if !debug then print_endline "Failed to merge"; m
        end
      | _ ->
        if !debug then (
          print_endline "Not Merging";
          print_endline ("- " ^ print_transition tr1 ~dev:true);
          print_endline ("- " ^ print_transition tr2 ~dev:true)
        );

        m
    ) m tr2_lst in m) m tr1_lst in
  m

let optimize' (m : model) = optimize_at m (m.model_init_state)

let optimize (m : model) =
let m = make_variables_unique m in
  let rec op m =
    let m' = optimize' m in
    begin if List.length m'.model_transitions < List.length m.model_transitions then
      op m'
    else
      m'
    end in
    op m




(* move equality and inequality facts from precondition to tags because Tamarin cannot handle
  (N)Eq fact generation rules correctly for fresh values *)
let move_eq_facts_transition (tr : transition) : transition =
  let new_pre, eq_facts = List.fold_left (fun (new_pre, eq_facts) f ->
    match f with
    | EqFact _ -> new_pre, f::eq_facts
    | NeqFact _ -> new_pre, f::eq_facts
    | _ -> (f::new_pre, eq_facts)
   ) ([], []) tr.transition_pre in

  {
    tr with
    transition_pre=new_pre ;
    transition_label=tr.transition_label@eq_facts
  }

let move_eq_facts (m : model) =
  {
    m with
    model_transitions = List.map move_eq_facts_transition m.model_transitions
  }
