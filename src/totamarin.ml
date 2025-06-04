open Tamarin

let get_return_var () = Var ("return" ^ !separator ^ "var")

let expr_pair a b = List [a ; b]
let index_inc index scope =
  match scope with
  | None ->
    begin match index with
    | (l,i)::lst -> (l,i+1)::lst
    | _ -> assert false
    end
  | Some s -> (s, 0)::index

let next_state ?(shift=(0,0,0)) st scope  =
  let (a, b, c) = shift in
  let (meta_num, loc_num, top_num) = st.state_vars in
  {st with state_index = index_inc st.state_index scope;
           state_vars = (meta_num + a, loc_num + b, top_num + c)}
  (* {st with state_index = index_inc st.state_index scope} *)

(* let next_state_app st scope num =
  {st with state_index = index_inc st.state_index scope} *)


let rec translate_expr ?(ch=false) {Location.data=e; Location.loc=_loc} =
  let translate_expr' = function
    | Syntax.ExtConst s -> Apply (s, [])
    | Syntax.Const _s -> assert false
    | Syntax.TopVariable (_v, i) -> TopVar i
    | Syntax.LocVariable (_v, i) -> LocVar i
    | Syntax.MetaVariable (_v, i) -> MetaVar i
    | Syntax.MetaNewVariable (_v, i) -> MetaNewVar i
    | Syntax.Boolean _b -> assert false
    | Syntax.String s -> String s
    | Syntax.Integer _z -> assert false
    | Syntax.Float _f -> assert false
    | Syntax.Apply (o, el) -> Apply (o, List.map (translate_expr ~ch:ch) el)
    | Syntax.Tuple el ->
       List (List.map (translate_expr ~ch:ch) el)
    | Syntax.Channel (c, None) -> if ch then Var c else String c
    | Syntax.Channel (c, Some e) -> expr_pair (String c) (translate_expr ~ch e)
    | Syntax.ParamConst (_cid, _e) -> assert false
    | Syntax.Param _ -> Param
  in translate_expr' e

  (* ConstantFact (String s, Var s) *)
let rec translate_expr2 ?(ch=false) ?(num=0) {Location.data=e; Location.loc=_loc} =
  let translate_expr2' = function
    | Syntax.ExtConst s -> Apply (s, []), [], num
    | Syntax.Const s -> Var s, [ConstantFact (String s, Var s)], num
    | Syntax.TopVariable (_v, i) -> TopVar i, [], num
    | Syntax.LocVariable (_v, i) -> LocVar i, [], num
    | Syntax.MetaVariable (_v, i) -> MetaVar i, [], num
    | Syntax.MetaNewVariable (_v, i) -> MetaNewVar i, [], num
    | Syntax.Boolean _b -> assert false
    | Syntax.String s -> String s, [], num
    | Syntax.Integer z -> Integer z, [], num
    | Syntax.Float _f -> assert false
    | Syntax.Apply (o, el) ->
       let (el, sl, n) = List.fold_left (fun (el, sl, n) e ->
                          let e, s, n = translate_expr2 ~ch:ch ~num:n e in
                          (el @ [e], sl @ s, n)) ([], [], num) el in
       Apply (o, el), sl, n
    | Syntax.Tuple el ->
       let (el, sl, n) = List.fold_left (fun (el, sl, n) e ->
                          let e, s, n = translate_expr2 ~ch:ch ~num:n e in
                          (el @ [e], sl @ s, n)) ([], [], num) el in
       List el, sl, n
    | Syntax.Channel (c, None) ->
        if ch then Var c, [], num else String c, [], num
    | Syntax.Channel (c, Some e) ->
        let e', l, n = (translate_expr2 ~ch:ch ~num:num e) in
        (* let var_name = (cid ^ !separator ^ string_of_int num) in *)
        expr_pair (String c) e', l, n
    | Syntax.ParamConst (cid, e) ->
      let e', l, n = (translate_expr2 ~ch:ch ~num:(num+1) e) in
      let var_name = (cid ^ !separator ^ string_of_int num) in
      Var var_name, (ConstantFact (expr_pair (String cid) e', Var var_name))::l, n
    | Syntax.Param _ -> Param, [], num

  in translate_expr2' e



(* let make_rule_name eng scope =
  eng.namespace^engine_state_aux eng ^ (match scope with Some scope -> (mult_list_with_concat (List.map string_of_int scope) "_") | None -> "") *)

let _lctx_to_var_list lctx = List.map (fun s -> Var s) lctx

let rec var_list_replace lctx s e =
  match lctx with
  | Var w :: l -> (if w = s then e else Var w) :: (var_list_replace l s e)
  | _ :: _l -> assert false
  | [] -> []

(* xxx not used *)
let _ = var_list_replace

let translate_fact ?(num=0) namespace f =
  match f.Location.data with
  | Syntax.Fact(id, el) ->
    let el, gv, n = List.fold_left (fun (el, gv, n) e -> let e, g, n = translate_expr2 ~num:n e in
                                  (el @ [e], gv @ g, n)) ([],[], num) el in
    Fact (id, namespace, el), gv, [], n

  | Syntax.GlobalFact(id, el) ->
    let el, gv, n = List.fold_left (fun (el, gv, n) e -> let e, g, n = translate_expr2 ~num:n e in
                                  (el @ [e], gv @ g, n)) ([],[], num) el in
    GlobalFact (id, el), gv, [], n

  | Syntax.ChannelFact(ch, id, el) ->
    let el, gv, n = List.fold_left (fun (el, gv, n) e -> let e, g, n = translate_expr2 ~num:n e in
                                  (el @ [e], gv @ g, n)) ([],[], num) el in
    let e, g, n = translate_expr2 ~num:n ch in

    ChannelFact (id, e, el), gv@g, [e], n

  | Syntax.EqFact (e1, e2) ->
      let es, gv, n = List.fold_left (fun (el, gv, n) e -> let e, g, n = translate_expr2 ~num:n e in
                                       (el @ [e], gv @ g, n)) ([],[], num) [e1; e2] in
      let e1, e2 = match es with [e1; e2] -> e1, e2 | _ -> assert false in
      ResFact (0, [e1; e2]), gv, [], n

  | Syntax.NeqFact (e1, e2) ->
      let es, gv, n = List.fold_left (fun (el, gv, n) e -> let e, g, n = translate_expr2 ~num:n e in
                                       (el @ [e], gv @ g, n)) ([],[], num) [e1; e2] in
      let e1, e2 = match es with [e1; e2] -> e1, e2 | _ -> assert false in
      ResFact (1, [e1; e2]), gv, [], n

  | Syntax.FileFact (p, d) ->
      let p, g1, n = translate_expr2 ~num:num p in
      let d, g2, n = translate_expr2 ~num:n d in
      FileFact (namespace, p, d), g1@g2, [p], n

  | _ -> assert false

let translate_facts ?(num=0) namespace fl =
  List.fold_left (fun (fl, gv, acps, n) f ->
              let (f, gv', acps', n) = translate_fact ~num:n namespace f in
              (fl @ [f], gv@gv', acps@acps', n)) ([],[],[], num) fl

let rec expr_shift_meta shift e =
  let e' =
  match e.Location.data with
  | Syntax.MetaVariable (v, i) -> Syntax.MetaVariable (v, i+ shift)
  | Syntax.Apply (o, el) ->
    Syntax.Apply (o, List.map (expr_shift_meta shift) el)
  | Syntax.Tuple el ->
    Syntax.Tuple (List.map (expr_shift_meta shift) el)
  | _ -> e.Location.data
  in Location.locate ~loc:e.Location.loc e'

let _fact_shift_meta shift f =
  match f.Location.data with
  | Syntax.Fact(id, el) ->
    Syntax.Fact(id, (List.map (expr_shift_meta shift) el))

  | Syntax.GlobalFact(id, el) ->
    Syntax.GlobalFact(id, (List.map (expr_shift_meta shift) el))

  | Syntax.ChannelFact(ch, id, el) ->
    Syntax.ChannelFact(expr_shift_meta shift ch, id, (List.map (expr_shift_meta shift) el))

  (* | Syntax.PathFact (path, id, el) ->
    Syntax.PathFact(expr_shift_meta shift path, id, (List.map (expr_shift_meta shift) el)) *)

  | Syntax.EqFact (e1, e2) ->
      Syntax.EqFact(expr_shift_meta shift e1, expr_shift_meta shift e2)
  | Syntax.NeqFact (e1, e2) ->
      Syntax.NeqFact(expr_shift_meta shift e1, expr_shift_meta shift e2)
  | Syntax.FileFact (e1, e2) ->
      Syntax.FileFact(expr_shift_meta shift e1, expr_shift_meta shift e2)

  | _ -> assert false

let rec tamarin_expr_shift_meta shift e =
  match e with
  | MetaVar i -> MetaVar (i + shift)
  | Apply (s, el) ->
    Apply (s, List.map (tamarin_expr_shift_meta shift) el)
  | List el -> List (List.map (tamarin_expr_shift_meta shift) el)
  | _ -> e

(* xxx not used *)
let _ = tamarin_expr_shift_meta

let rec pop_hd n lst =
  if n > 0 then
  match lst with
  | _ :: lst -> pop_hd (n-1) lst
  | [] -> assert false
  else if n = 0 then lst else assert false

(* xxx not used *)
let _ = pop_hd

(*
  given a model, the current state that is promised to be already in the model,
  this function returns an extended model
*)
let rec translate_cmd mo (st : state) funs syscalls attacks vars scope syscall pol {Location.data=c; Location.loc=_loc} =
  let return_var = get_return_var () in
  let (meta_num, loc_num, top_num) = vars in

  match c with
  | Syntax.Return e ->
    let e, gv, _ = translate_expr2 e in
    let (st_f : state) = next_state st scope in
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_id = List.length mo.model_transitions;
      transition_namespace = mo.model_name;
      transition_name = "return";
      transition_from = st;
      transition_to = st_f;
      transition_pre = gv;
      transition_post = [];
      transition_state_transition = mk_state_transition_from_action (ActionReturn e) vars;
      transition_label = [];
      transition_is_loop_back = false
    } in
    (mo, st_f)


  | Syntax.Skip ->
    let st_f = next_state st scope in
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_id = List.length mo.model_transitions;
      transition_namespace = mo.model_name;
      transition_name = "skip";
      transition_from = st;
      transition_to = st_f;
      transition_pre = [];
      transition_post = [];
      transition_state_transition = mk_state_transition_from_action (ActionReturn Unit) vars;
      transition_label = [];
      transition_is_loop_back = false

    } in
    (mo, st_f)

  | Syntax.Sequence (c1, c2) ->
    let (mo, st) = translate_cmd mo st funs syscalls attacks vars scope syscall pol  c1 in
    let (mo, st) = translate_cmd mo st funs syscalls attacks vars None syscall pol  c2 in
    (mo, st)

  | Syntax.Put fl ->
    let fl, gv, acps, _ = translate_facts mo.model_name fl in
    let acps = List.map (fun target -> AccessFact(mo.model_name, Param, target, syscall)) acps in
    let st_f = next_state st scope in
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_id = List.length mo.model_transitions;
      transition_namespace = mo.model_name;
      transition_name = "put";
      transition_from = st;
      transition_to = st_f;
      transition_pre = gv @ acps;
      transition_post = fl;
      transition_state_transition = mk_state_transition_from_action (ActionReturn Unit) vars;
      transition_label = [];
      transition_is_loop_back = false

    } in
    (mo, st_f)

  | Syntax.Let (_v, e, c) ->

    let e, gv, _ = translate_expr2 e in

    let st_f = next_state ~shift:(0,1,0) st scope  in
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_id = List.length mo.model_transitions;
      transition_namespace = mo.model_name;
      transition_name = "let_intro";
      transition_from = st;
      transition_to = st_f;
      transition_pre = gv;
      transition_post = [];
      transition_state_transition = mk_state_transition_from_action (ActionIntro [e]) vars;
      transition_label = [];
      transition_is_loop_back = false

    } in

    let (mo, st) = translate_cmd mo st_f funs syscalls attacks (meta_num, loc_num+1, top_num) None syscall pol c in

    let st_f = next_state ~shift:(0,-1,0) st scope in
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_id = List.length mo.model_transitions;
      transition_namespace = mo.model_name;
      transition_name = "let_out";
      transition_from = st;
      transition_to = st_f;
      transition_pre = [];
      transition_post = [];
      transition_state_transition = mk_state_transition_from_action (ActionPopLoc 1) st.state_vars;
      transition_label = [];
      transition_is_loop_back = false

    } in
    (mo, st_f)

  | Syntax.Assign ((_v, di), e) ->

    let e, gv, _ = translate_expr2 e in
    let st_f = next_state st scope in
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_id = List.length mo.model_transitions;
      transition_namespace = mo.model_name;
      transition_name = "assign";
      transition_from = st;
      transition_to = st_f;
      transition_pre = gv;
      transition_post = [];
      transition_state_transition = mk_state_transition_from_action (ActionAssign (di, e)) st.state_vars;
      transition_label = [];
      transition_is_loop_back = false

    } in
    (mo, st_f)

  | Syntax.FCall (ov, f, el) ->
    let el, gv, _ = List.fold_left (fun (el, gv, n) e -> let e, g, n = translate_expr2 ~num:n e in
                                  (el @ [e], gv @ g, n)) ([],[], 0) el in
    let el = List.rev el in

    let (_f, _args, cmd) = List.find (fun (f', _args, _cmd) -> f = f') funs in

    let st_f = next_state ~shift:(0,List.length el,0) st scope in
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_id = List.length mo.model_transitions;
      transition_namespace = mo.model_name;
      transition_name = "fcall_intro";
      transition_from = st;
      transition_to = st_f;
      transition_pre = gv;
      transition_post = [];
      transition_state_transition = mk_state_transition_from_action (ActionIntro el) st.state_vars;
      transition_label = [];
      transition_is_loop_back = false

    } in

    let (mo, st) = translate_cmd mo st_f funs syscalls attacks (meta_num, loc_num + (List.length el), top_num) None syscall pol cmd in

    let st_f = next_state ~shift:(0,- (List.length el),0) st scope in
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_id = List.length mo.model_transitions;
      transition_namespace = mo.model_name;
      transition_name = "fcall_out";
      transition_from = st;
      transition_to = st_f;
      transition_pre = [];
      transition_post = [];
      transition_state_transition = mk_state_transition_from_action (match ov with
      | None -> ActionPopLoc (List.length el)
      | Some (_, v) -> ActionSeq (ActionPopLoc (List.length el), ActionAssign (v, return_var))
      ) st.state_vars;
      transition_label = [];
      transition_is_loop_back = false

    } in
    (mo, st_f)

  | Syntax.SCall (ov, o, el) ->
    let el, gv, _ = List.fold_left (fun (el, gv, n) e -> let e, g, n = translate_expr2 ~num:n e in
                                  (el @ [e], gv @ g, n)) ([],[], 0) el in
    let el = List.rev el in

    let (_f, _args, cmd) = List.find (fun (f', _args, _cmd) -> o = f') syscalls in

    let st_i = next_state ~shift:(0,List.length el,0) st (Some [0]) in

    let mo = add_state mo st_i in
    let mo = add_transition mo {
      transition_id = List.length mo.model_transitions;
      transition_namespace = mo.model_name;
      transition_name = "scall_intro";
      transition_from = st;
      transition_to = st_i;
      transition_pre = gv;
      transition_post = [];
      transition_state_transition = mk_state_transition_from_action (ActionIntro el) st.state_vars;
      transition_label = [];
      transition_is_loop_back = false

    } in

    let (mo, st_m) = translate_cmd mo st_i funs syscalls attacks (meta_num, loc_num + (List.length el), top_num) None o pol cmd in

    let st_f = next_state st None in
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_id = List.length mo.model_transitions;
      transition_namespace = mo.model_name;
      transition_name = "scall_out";
      transition_from = st_m;
      transition_to = st_f;
      transition_pre = [];
      transition_post = [];
      transition_state_transition = mk_state_transition_from_action (match ov with
      | None -> ActionPopLoc (List.length el)
      | Some (_, v) -> ActionSeq (ActionPopLoc (List.length el), ActionAssign (v, return_var))
      ) st_m.state_vars;
      transition_label = [];
      transition_is_loop_back = false

    } in

    (* if this system call is attacked *)
    begin match List.find_all (fun (a, t, _, _cmd) -> t = o && List.exists (fun (s1,s2) -> s1 = mo.model_type && s2 = a) pol.Context.pol_attack) attacks with
    | [] ->  (mo, st_f)
    | lst ->
      let scope_lst = List.map (fun i -> Some [i+1]) (List.init (List.length lst) (fun i -> i)) in
      let mo = List.fold_left2 (fun mo scope (_a, _, _, c) ->
        let st_i2 = next_state ~shift:(0,List.length el,0) st scope in
        let mo = add_state mo st_i2 in
        let mo = add_transition mo {
          transition_id = List.length mo.model_transitions;
          transition_namespace = mo.model_name;
          transition_name = "attack_intro";
          transition_from = st;
          transition_to = st_i2;
          transition_pre =  gv;
          transition_post = [];
          transition_state_transition = mk_state_transition_from_action (ActionIntro el) st.state_vars;
          transition_label = [];
          transition_is_loop_back = false
        } in
        let (mo, st_m) = translate_cmd mo st_i2 funs syscalls attacks (meta_num, loc_num + (List.length el), top_num) None o pol c in
        add_transition mo {
          transition_id = List.length mo.model_transitions;
          transition_namespace = mo.model_name;
          transition_name = "attack_out";
          transition_from = st_m;
          transition_to = st_f;
          transition_pre = [];
          transition_post = [];
          transition_state_transition = mk_state_transition_from_action (match ov with
          | None -> ActionPopLoc (List.length el)
          | Some (_, v) -> ActionSeq (ActionPopLoc (List.length el), ActionAssign (v, return_var))
          ) st_m.state_vars;
          transition_label = [];
          transition_is_loop_back = false
        }) mo scope_lst lst in
        (mo, st_f)
      end

  | Syntax.Case (cs) ->
    let scope_lst =
      begin match scope with
      | None ->
        List.map (fun i -> Some [i]) (List.init (List.length cs) (fun i -> i))
      | Some l ->
        List.map (fun i -> Some (i :: l)) (List.init (List.length cs) (fun i -> i))
      end in

    (* final state for all branches *)
    let st_f = next_state st None in

    let mo = List.fold_left2 (fun mo scope (vl, fl, c) ->
      let (mo, st) = translate_guarded_cmd mo st funs syscalls attacks vars scope syscall pol (vl, fl, c) in
      add_transition mo {
        transition_id = List.length mo.model_transitions;
        transition_namespace = mo.model_name;
        transition_name = "case_out";
        transition_from = st;
        transition_to = st_f;
        transition_pre = [];
        transition_post = [];
        transition_state_transition = mk_state_transition_from_action (ActionPopMeta (List.length vl)) st.state_vars;
        transition_label = [];
        transition_is_loop_back = false
      }) mo scope_lst cs in

    (add_state mo st_f, st_f)

 | Syntax.While (cs1, cs2) ->
    let mindex = st.state_index in
    let st_i = next_state st scope in
    let tid = List.length mo.model_transitions in
    let mo = add_transition mo {
      transition_id = tid;
      transition_namespace = mo.model_name;
      transition_name = "repeat_in";
      transition_from = st;
      transition_to = st_i;
      transition_pre = [];
      transition_post = [];
      transition_state_transition = mk_state_transition_from_action (ActionReturn Unit) st.state_vars;
      transition_label = [
        (LoopFact (mo.model_name, mindex, 0))
      ];
      transition_is_loop_back = false
    } in
    let st = st_i in

    let scope_lst1 =
        List.map (fun i -> Some [i]) (List.init (List.length cs1) (fun i -> i)) in
    let scope_lst2 =
        List.map (fun i -> Some [i]) (List.init (List.length cs2) (fun i -> i + (List.length cs1))) in

    let st_f = next_state st None in

    let mo = List.fold_left2 (fun mo scope (vl, fl, c) ->
      let (mo, st_f) = translate_guarded_cmd mo st funs syscalls attacks vars scope syscall pol (vl, fl, c) in
      add_transition mo {
        transition_id = List.length mo.model_transitions;
        transition_namespace = mo.model_name;
        transition_name = "repeat";
        transition_from = st_f;
        transition_to = st;
        transition_pre = [];
        transition_post = [];
        transition_state_transition = mk_state_transition_from_action (ActionPopMeta (List.length vl)) st_f.state_vars;
        transition_label = [
          (LoopFact (mo.model_name, mindex, 1))
        ];
        transition_is_loop_back = true
      }) mo scope_lst1 cs1 in

    let mo = List.fold_left2 (fun mo scope (vl, fl, c) ->
      let (mo, st) = translate_guarded_cmd mo st funs syscalls attacks vars scope syscall pol (vl, fl, c) in
      add_transition mo {
        transition_id = List.length mo.model_transitions;
        transition_namespace = mo.model_name;
        transition_name = "repeat_out";
        transition_from = st;
        transition_to = st_f;
        transition_pre = [];
        transition_post = [];
        transition_state_transition = mk_state_transition_from_action (ActionPopMeta (List.length vl)) st.state_vars;
        transition_label = [
          (LoopFact (mo.model_name, mindex, 2))
        ];
        transition_is_loop_back = false
      }) mo scope_lst2 cs2 in

    (add_state mo st_f, st_f)

 | Syntax.Event (fl) ->
    let fl, gv, _acps, _ = translate_facts mo.model_name fl in
    let st_f = next_state st scope in
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_id = List.length mo.model_transitions;
      transition_namespace = mo.model_name;
      transition_name = "event";
      transition_from = st;
      transition_to = st_f;
      transition_pre = gv;
      transition_post = [];
      transition_state_transition = mk_state_transition_from_action (ActionReturn Unit) st.state_vars;
      transition_label = fl;
      transition_is_loop_back = false
    } in
  (mo, st_f)

  (* | New of Name.ident * Name.ident * expr list * cmd
  | Get of Name.ident list * expr * Name.ident * cmd
  | Del of expr * Name.ident *)

 | Syntax.New (_v, fid_el_opt, c) ->
  let fid, el = Option.value fid_el_opt ~default:("",[]) in
  let el, gv, _ = List.fold_left (fun (el, gv, n) e -> let e, g, n = translate_expr2 ~num:n e in
    (el @ [e], gv @ g, n)) ([],[], 0) el in

  (* | InjectiveFact of
    string * (* fact name *)
    string * (* namespace *)
    expr list (* arguments *)
  | FreshFact of expr *)

  let st_f = next_state ~shift:(1,0,0) st scope  in
  let mo = add_state mo st_f in
  let mo = add_transition mo {
    transition_id = List.length mo.model_transitions;
    transition_namespace = mo.model_name;
    transition_name = "new_intro";
    transition_from = st;
    transition_to = st_f;
    transition_pre = (FreshFact (MetaNewVar 0))::gv;
    transition_post = (if fid = "" then [] else [InjectiveFact (fid, mo.model_name, (MetaNewVar 0), List el)]);
    transition_state_transition = mk_state_transition_from_action (ActionAddMeta 1) vars;
    transition_label = [];
    transition_is_loop_back = false
  } in

  let (mo, st) = translate_cmd mo st_f funs syscalls attacks (meta_num+1, loc_num, top_num) None syscall pol  c in

  let st_f = next_state ~shift:(-1,0,0) st scope in
  let mo = add_state mo st_f in
  let mo = add_transition mo {
    transition_id = List.length mo.model_transitions;
    transition_namespace = mo.model_name;
    transition_name = "new_out";
    transition_from = st;
    transition_to = st_f;
    transition_pre = [];
    transition_post = [];
    transition_state_transition = mk_state_transition_from_action (ActionPopMeta 1) st.state_vars;
    transition_label = [];
    transition_is_loop_back = false
  } in
  (mo, st_f)



  | Syntax.Get (vl, id, fid, c) ->
    let e, g, _ = translate_expr2 id in

  (* | InjectiveFact of
    string * (* fact name *)
    string * (* namespace *)
    expr list (* arguments *)
  | FreshFact of expr *)

  let st_f = next_state ~shift:(List.length vl,0,0) st scope  in
  let mo = add_state mo st_f in
  let mo = add_transition mo {
    transition_id = List.length mo.model_transitions;
    transition_namespace = mo.model_name;
    transition_name = "get_intro";
    transition_from = st;
    transition_to = st_f;
    transition_pre = [InjectiveFact (fid, mo.model_name, e, List (List.map (fun i -> MetaNewVar i) (int_to_list (List.length vl))))] @ g;
    transition_post = [InjectiveFact (fid, mo.model_name, e, List (List.map (fun i -> MetaNewVar i) (int_to_list (List.length vl))))];
    transition_state_transition = mk_state_transition_from_action (ActionAddMeta (List.length vl)) vars;
    transition_label = [];
    transition_is_loop_back = false
  } in

  let (mo, st) = translate_cmd mo st_f funs syscalls attacks (meta_num + (List.length vl), loc_num, top_num) None syscall pol c in

  let st_f = next_state ~shift:(-(List.length vl),0,0) st scope in
  let mo = add_state mo st_f in
  let mo = add_transition mo {
    transition_id = List.length mo.model_transitions;
    transition_namespace = mo.model_name;
    transition_name = "get_out";
    transition_from = st;
    transition_to = st_f;
    transition_pre = [];
    transition_post = [];
    transition_state_transition = mk_state_transition_from_action (ActionPopMeta (List.length vl)) st.state_vars;
    transition_label = [];
    transition_is_loop_back = false
  } in
  (mo, st_f)

  | Syntax.Del (id, fid) ->
    let e, g, _ = translate_expr2 id in
    let st_f = next_state st scope  in
    let mo = add_state mo st_f in
    let mo = add_transition mo {
      transition_id = List.length mo.model_transitions;
      transition_namespace = mo.model_name;
      transition_name = "del";
      transition_from = st;
      transition_to = st_f;
      transition_pre = [InjectiveFact (fid, mo.model_name, e, (MetaNewVar 0)) ] @g;
      transition_post = [];
      transition_state_transition = mk_state_transition_from_action (ActionReturn Unit) vars;
      transition_label = [];
      transition_is_loop_back = false
    } in
    (mo, st_f)



and translate_guarded_cmd mo st funs syscalls attacks vars scope syscall pol (vl, fl, c) =
  let (meta_num, loc_num, top_num) = vars in

  let fl, gv, acps, _ = translate_facts mo.model_name fl in
  let acps = List.map (fun target -> AccessFact(mo.model_name, Param, target,syscall)) acps in
  let st_f = next_state ~shift:(List.length vl, 0, 0) st scope in
  let mo = add_state mo st_f in
  (* let eng_f = engine_index_inc eng scope in *)
  let mo = add_transition mo {
    transition_id = List.length mo.model_transitions;
    transition_namespace = mo.model_name;
    transition_name = "guarded";
    transition_from = st;
    transition_to = st_f;
    transition_pre = fl @ gv @ acps;
    transition_post = [];
    transition_state_transition = mk_state_transition_from_action (ActionAddMeta (List.length vl)) st.state_vars;
    transition_label = [];
    transition_is_loop_back = false

  } in
  let (mo, st_f) = translate_cmd mo st_f funs syscalls attacks (meta_num + List.length vl, loc_num, top_num) None syscall pol c in
  (mo, st_f)




let translate_process {
        Context.proc_pid=k;
        Context.proc_name=s;
        Context.proc_type=pty_unused;
        Context.proc_filesys=fls;
        Context.proc_variable=vars;
        Context.proc_function=fns;
        Context.proc_main=m;
        Context.proc_channels=_channels;

      } syscalls attacks pol =
  let namespace = String.capitalize_ascii (s ^ (if k = 0 then "" else string_of_int k)) in (* this must be unique *)
  (* let t = add_comment t ("- Process name: " ^ namespace) in  *)

  let mo, st = initial_model namespace pty_unused in

  (* installed channels: *)
  (* let (mo, st) = List.fold_left (fun (mo, st) c ->

  ) (mo, st) channels in *)


  (* initialize file system *)
  let (mo, st) = List.fold_left (fun (mo, st) (path, ty, e) ->
      (* let path = (mk_dir eng fsys path) in *)
      let st_f = next_state ~shift:(0,0,0) st None in
      let mo = add_state mo st_f in
      let e, gv, _ = translate_expr2 e in
      let path, _gv', _ = translate_expr2 path in

      (* let name = mk_fact_name  namespace^ replace_string '/' !separator path in  *)
      let mo = add_transition mo {
        transition_id = List.length mo.model_transitions;
        transition_namespace = mo.model_name;
        transition_name = "init_filesys";
        transition_from = st;
        transition_to = st_f;
        transition_pre = gv;
        transition_post = [FileFact(namespace, path, e)]
        @ List.map (fun (_, _, scall) -> AccessFact(mo.model_name, Param, path, scall)) (List.filter (fun (pty, tyl, _) -> pty = pty_unused && List.exists (fun s -> s = ty) tyl) pol.Context.pol_access)
        @ if List.exists (fun (pty, tyl) -> pty = pty_unused && List.exists (fun s -> s = ty) tyl) pol.Context.pol_access_all then [AccessFact(mo.model_name,Param,  path, "")] else []
        ;
        transition_state_transition = mk_state_transition_from_action (ActionReturn Unit) st.state_vars;
        transition_label = [];
        transition_is_loop_back = false
      } in
      (mo, st_f)) (mo, st) fls in

  (* initialize rule *)
  (* let mo = add_rule mo (name, "",
  [],
  [InitFact([String namespace; String path])],
  [FileFact(namespace, path, e)]) in *)



  (* initialize memory *)
  let (mo, st) = List.fold_left
                   (fun (mo, st) (_x, e) ->
          let st_f = next_state ~shift:(0,0,1) st None in
          let mo = add_state mo st_f in
          let e, gv, _ = translate_expr2 e in
          let mo = add_transition mo {
            transition_id = List.length mo.model_transitions;
            transition_namespace = mo.model_name;
            transition_name = "init_mem";
            transition_from = st;
            transition_to = st_f;
            transition_pre = gv;
            transition_post = [];
            transition_state_transition = mk_state_transition_from_action (ActionLetTop [e]) st.state_vars;
            transition_label = [];
            transition_is_loop_back = false

          } in
          (mo, st_f)) (mo, st) (List.rev vars) in


  (* translate the main function *)
  let (mo, _st) = translate_cmd mo st fns syscalls attacks (0, 0, List.length vars) None "" pol  m in

  mo
  (* List.fold_left (fun t r -> add_rule t
    (let (rname, pre, lab, post) = r in
    (rname, namespace, pre, lab, post))) t r  *)


let get_fact_names ctx =
  (List.map (fun (a,_,_) -> a) ctx.Context.ctx_fact) @
    (List.map fst ctx.Context.ctx_event) @
      (List.map fst ctx.Context.ctx_ext_syscall) @
        (List.fold_left (fun l proc ->
             [proc.Context.ctx_proctmpl_id] @
               List.map fst proc.Context.ctx_proctmpl_func @
                 l) [] ctx.Context.ctx_proctmpl)



let translate_sys {
  Context.sys_ctx = ctx ;
  Context.sys_def = def;
  Context.sys_pol = pol;
  Context.sys_proc = proc ;
  Context.sys_param_proc = param_proc ;
  Context.sys_lemma = lem
} (used_idents, used_string) =

  separator := (let names = get_fact_names ctx in
   let rec f s = if List.exists (fun u -> contains u s) names then f (s ^"_") else s in
    f "_");

  fresh_ident := (let rec f s = if List.exists (fun u -> u = s) used_idents then f (s^"_") else s in
          f "rab") ;

  fresh_string := (let rec f s = if List.exists (fun u -> u = s) used_string then f (s^"_") else s in
                                  f "rab") ;

  fresh_param := (let rec f s = if List.exists (fun u -> u = s) used_string then f (s^"_") else s in
  f "param") ;


  let sep = !separator in

  let t : tamarin = empty_tamarin in

  (* process signature *)
  let t = List.fold_left (fun t (f, k) -> add_fun t (f, k)) t (List.rev ctx.Context.ctx_ext_func) in
  let t = List.fold_left (fun t c -> add_const t c) t (List.rev ctx.Context.ctx_ext_const) in
  let t = List.fold_left (fun t (_, e1, e2) -> add_eqn t (translate_expr e1, translate_expr e2)) t (List.rev def.Context.def_ext_eq) in

  (* global constants *)
  let t = add_comment t "Global Constants:" in

  let t = List.fold_left (fun t (v, e) ->
              match e with
              | None -> (* when v is fresh *)
          add_rule t
          ("Const"^sep^v, "", [ResFact(2, [Var v])],
            [InitFact [String ("Const"^sep^v)];
            InitFact [List [String ("Const"^sep^v); Var v]]; mk_constant_fact v],
            [mk_constant_fact v])
              | Some e -> (* when v is defined *)
          let e, gv, _ = translate_expr2 e in
                add_rule t ("Const"^sep^v, "", gv, [ConstantFact(String v, e)], [ConstantFact(String v, e)])) t (List.rev def.Context.def_const) in

  let t = add_comment t "Parametric global Constants:" in

  let t = List.fold_left (fun t (v, e) ->
    match e with
    | None -> (* when v is fresh *)
      add_rule t
      ("Const"^sep^v, "",
        [ResFact(2, [Var v])],
        [InitFact [expr_pair (String v) Param]; ConstantFact (expr_pair (String v) Param, Var v)],
        [ConstantFact (expr_pair (String v) Param, Var v)])
    | Some (_p, e) -> (* when v is defined *)
      let e, gv, _ = translate_expr2 e in
      add_rule t ("Const"^sep^v, "", gv,
        [InitFact [expr_pair (String v) Param]; ConstantFact (expr_pair (String v) Param, e)],
        [ConstantFact (expr_pair (String v) Param, e)]))
      t (List.rev def.Context.def_param_const) in


  let t = add_comment t "Access control:" in
  (* access control *)

  (* let t = add_comment t "Processes:" in *)
  let mos = List.fold_left (fun mos p ->  (translate_process p def.Context.def_ext_syscall def.Context.def_ext_attack pol)::mos) [] (List.rev proc) in
  let facts_gv_list = List.fold_left (fun (facts_gv_list) p ->
    let namespace = String.capitalize_ascii (p.Context.proc_name ^ (if p.Context.proc_pid = 0 then "" else string_of_int p.Context.proc_pid)) in
    let new_pol = pol.Context.pol_access @ (List.map (fun (a, b) -> (a, b, "")) pol.Context.pol_access_all) in
    let facts_gv_list' = List.fold_left (fun (facts_gv_list) c ->
      (* List.fold_left  *)
      begin
      match c with
      | Syntax.ChanArgPlain (cname, cty) ->
        false, List.map (fun (_, _, scall) ->
          print_fact' (AccessFact(namespace, String !fresh_string, String cname, scall)))
          (List.filter (fun (pty, tyl, _scall ) -> pty = p.Context.proc_type && List.exists (fun v -> v = cty) tyl) new_pol), []
      | Syntax.ChanArgParam (cname, cty) ->
        true, List.map (fun (_, _, scall) ->
          print_fact' (AccessFact(namespace, String !fresh_string,List [String cname; Var !fresh_ident], scall)))
          (List.filter (fun (pty, tyl, _scall ) -> pty = p.Context.proc_type && List.exists (fun v -> v = cty) tyl) new_pol), []
      | Syntax.ChanArgParamInst (cname, e, cty) ->
        let e, gv', _ = translate_expr2 e in
        false, List.map (fun (_, _, scall) ->
          print_fact' (AccessFact(namespace, String !fresh_string,List [String cname; e], scall)))
          (List.filter (fun (pty, tyl, _scall ) -> pty = p.Context.proc_type && List.exists (fun v -> v = cty) tyl) new_pol), gv'
        end :: facts_gv_list
      ) [] (p.Context.proc_channels) in
    facts_gv_list@facts_gv_list'
    ) ([]) (List.rev proc) in


  let t = add_rule' t
    ("Init"^ !separator ^"system", "system", [], [print_fact' (InitFact ([String "system"]))],
    (* initializing tokens..  *)
    (List.map (fun m ->
      let st = m.model_init_state in
      (if !Config.tag_transition
      then mk_state_transition ~param:!fresh_string st (Unit, [], [], []) true false
      else mk_state ~param:!fresh_string st (Unit, [], [], []))) mos) @
      [print_fact' (AccessGenFact ("system"^ !separator, String !fresh_string)) ]
      ) in

  let t, _ = List.fold_left (fun (t, n) (b, facts, gv) ->
    List.fold_left (fun (t, n) (fact : fact') ->
      add_rule' t
        ("Init"^ !separator ^"system"^ !separator^"ACP" ^ !separator^ string_of_int n, "system",
        (List.map print_fact' gv)@
        [print_fact' (AccessGenFact ("system"^ !separator, String !fresh_string))],
        [print_fact'
          (if b then (InitFact ([List [String ("system" ^ !separator^ "ACP" ^ !separator ^ string_of_int n) ; Var !fresh_ident]]))
          else (InitFact [(String ("system" ^ !separator ^ "ACP" ^ !separator ^ string_of_int n))]))
          ],
        [fact]), n+1) (t, n) facts) (t,0) facts_gv_list in




  let t = List.fold_left (fun t m -> add_model t m) t mos in

  let t, _ = List.fold_left (fun (t, n) pl ->

    let mos = List.fold_left (fun mos p ->  (translate_process p def.Context.def_ext_syscall def.Context.def_ext_attack pol)::mos) [] (List.rev pl) in
    let facts_gv_list = List.fold_left (fun facts_gv_list p ->
      let namespace = String.capitalize_ascii (p.Context.proc_name ^ (if p.Context.proc_pid = 0 then "" else string_of_int p.Context.proc_pid)) in
      (* print_string namespace; *)
      let new_pol = pol.Context.pol_access @ (List.map (fun (a, b) -> (a, b, "")) pol.Context.pol_access_all) in
      let facts_gv_list' = List.fold_left (fun facts_gv_list c ->
        begin match c with
        | Syntax.ChanArgPlain (cname, cty) ->

          false, List.map (fun (_, _, scall) ->
            print_fact' (AccessFact(namespace, Param, String cname, scall)))
            (List.filter (fun (pty, tyl, _scall ) -> pty = p.Context.proc_type && List.exists (fun v -> v = cty) tyl) new_pol), []
        | Syntax.ChanArgParam (cname, cty) ->

          true, List.map (fun (_, _, scall) ->
            print_fact' (AccessFact(namespace, Param, List [String cname; Var !fresh_ident], scall)))
            (List.filter (fun (pty, tyl, _scall ) -> pty = p.Context.proc_type && List.exists (fun v -> v = cty) tyl) new_pol), []
        | Syntax.ChanArgParamInst (cname, e, cty) ->

          let e, gv', _ = translate_expr2 e in
          false, List.map (fun (_, _, scall) ->
            print_fact' (AccessFact(namespace, Param, List [String cname; e], scall)))

            (List.filter (fun (pty, tyl, _scall ) -> pty = p.Context.proc_type && List.exists (fun v -> v = cty) tyl) new_pol), gv'

        end :: facts_gv_list
        ) ([]) (p.Context.proc_channels) in
      (facts_gv_list@facts_gv_list')
      ) ([]) (List.rev pl) in


    let t = add_rule' t
      ("Init"^ !separator ^"system"^string_of_int n, "system"^string_of_int n,
      [("Fr", [Param], config_linear)],
      [print_fact' (InitFact ([List [String ("system"^string_of_int n); Param]]))],
      [print_fact' (AccessGenFact ("system"^string_of_int n^ !separator, Param)) ] @ List.map (fun m ->
        let st = m.model_init_state in
        (if !Config.tag_transition
        then mk_state_transition st (Unit, [], [], []) true false
        else mk_state st (Unit, [], [], []))) mos) in

    let t, _ = List.fold_left (fun (t, m) (b, facts, gv) ->
      List.fold_left (fun (t, m) (fact : fact') ->
        add_rule' t
          ("Init"^ !separator ^"system"^string_of_int n^ !separator^"ACP" ^ !separator^ string_of_int m, "system"^string_of_int n,
          (List.map print_fact' gv)@
          [print_fact' (AccessGenFact ("system"^string_of_int n^ !separator, Param))],
          [print_fact'
            (if b then (InitFact ([List [String ("system"^string_of_int n ^ !separator^ "ACP" ^ !separator ^ string_of_int m) ; Param ; Var !fresh_ident]]))
            else (InitFact [List [(String ("system"^string_of_int n ^ !separator ^ "ACP" ^ !separator ^ string_of_int m)) ; Param  ]]))
            ],
          [fact]), m+1) (t, m) facts) (t,0) facts_gv_list in


    let t = List.fold_left (fun t m -> add_model t m) t mos in
    (t, n+1)
  ) (t, 1) (List.rev param_proc) in


  (* translating lemmas now *)
  let t = List.fold_left (fun t l ->
    let l =
      match l.Location.data with
      | Syntax.PlainLemma (l, p) -> PlainLemma (l, p)
      | Syntax.ReachabilityLemma (l, cs, fs) ->
        let fs, gv, _, _ = translate_facts "" fs in
        ReachabilityLemma (l, cs, [], [], gv, fs)
      | Syntax.CorrespondenceLemma (l, vl,a, b) ->
        let a, gva =
          match translate_facts "" [a] with
          | [a], gva, _, _ -> a, gva
          | _ -> assert false
        in
        let b, gvb =
          match translate_facts "" [b] with
          | [b], gvb, _, _ -> b, gvb
          | _ -> assert false
        in
        CorrespondenceLemma (l, vl, (gva, a), (gvb, b))

          (* | ReachabilityLemma of string * string list * string list * string list * (string * expr list) list *)
          (* | CorrespondenceLemma of string * string list * (string * expr list) * (string * expr list) *)


      (* | Syntax.CorrespondenceLemma (l, vars, e1, e2) ->
        CorrespondenceLemma (l, vars,
            (match e1.Location.data with
            | Syntax.Event (id, el) -> (mk_fact_name id, List.map (translate_expr ~ch:false) el)),
            (match e2.Location.data with
            | Syntax.Event (id, el) -> (mk_fact_name id, List.map (translate_expr ~ch:false) el)))
      *)
    in add_lemma t l) t lem in
  t
