open Tamarin

let get_return_var () = Var ("return" ^ !separator ^ "var")
let expr_pair a b = List [ a; b ]

let next_state ?(shift_meta=0) ?(shift_loc=0) ?(shift_top=0) st scope =
  let { meta; loc; top } = st.state_vars in
  { st with
    state_index = Mindex.inc st.state_index scope
  ; state_vars =
      { meta = meta + shift_meta; loc = loc + shift_loc; top = top + shift_top }
  }
;;

let rec translate_expr ?(ch = false) (e : Syntax.expr) : expr =
  match e.Location.data with
  | Syntax.ExtConst s -> Apply (s, [])
  | Syntax.Const (_s, None) -> assert false
  | Syntax.Const (_cid, Some _e) -> assert false
  | Syntax.Variable (_v, Top i) -> TopVar i
  | Syntax.Variable (_v, Loc i) -> LocVar i
  | Syntax.Variable (_v, Meta i) -> MetaVar i
  | Syntax.Variable (_v, MetaNew i) -> MetaNewVar i
  | Syntax.Variable (_v, Param) -> Param
  | Syntax.Boolean _b -> assert false
  | Syntax.String s -> String s
  | Syntax.Integer _z -> assert false
  | Syntax.Float _f -> assert false
  | Syntax.Apply (o, el) -> Apply (o, List.map (translate_expr ~ch) el)
  | Syntax.Tuple el -> List (List.map (translate_expr ~ch) el)
  | Syntax.Channel (c, None) -> if ch then Var c else String c
  | Syntax.Channel (c, Some e) -> expr_pair (String c) (translate_expr ~ch e)
;;

(* ConstantFact (String s, Var s) *)
let rec translate_expr2 ?(ch = false) ?(num = 0) e : expr * fact list * int =
  match e.Location.data with
  | Syntax.ExtConst s -> Apply (s, []), [], num
  | Syntax.Const (s, None) -> Var s, [ ConstantFact (String s, Var s) ], num
  | Syntax.Const (cid, Some e) ->
      let e', fs, n = translate_expr2 ~ch ~num:(num + 1) e in
      let var_name = cid ^ !separator ^ string_of_int num in
      Var var_name, ConstantFact (expr_pair (String cid) e', Var var_name) :: fs, n
  | Syntax.Variable (_v, Top i) -> TopVar i, [], num
  | Syntax.Variable (_v, Loc i) -> LocVar i, [], num
  | Syntax.Variable (_v, Meta i) -> MetaVar i, [], num
  | Syntax.Variable (_v, MetaNew i) -> MetaNewVar i, [], num
  | Syntax.Variable (_v, Param) -> Param, [], num
  | Syntax.Boolean _b -> assert false
  | Syntax.String s -> String s, [], num
  | Syntax.Integer z -> Integer z, [], num
  | Syntax.Float _f -> assert false
  | Syntax.Apply (o, el) ->
      let es, fs, n =
        List.fold_left
          (fun (es, fs, n) e ->
             let e, fs', n = translate_expr2 ~ch ~num:n e in
             es @ [ e ], fs @ fs', n)
          ([], [], num)
          el
      in
      Apply (o, es), fs, n
  | Syntax.Tuple el ->
      let el, fs, n =
        List.fold_left
          (fun (es, fs, n) e ->
             let e, fs', n = translate_expr2 ~ch ~num:n e in
             es @ [ e ], fs @ fs', n)
          ([], [], num)
          el
      in
      List el, fs, n
  | Syntax.Channel (c, None) -> if ch then Var c, [], num else String c, [], num
  | Syntax.Channel (c, Some e) ->
      let e', fs, n = translate_expr2 ~ch ~num e in
      (* let var_name = (cid ^ !separator ^ string_of_int num) in *)
      expr_pair (String c) e', fs, n
;;

let translate_expr2s ~num es =
  List.fold_left
    (fun (es, fs, num) e ->
       let e, fs', num = translate_expr2 ~num e in
       es @ [ e ], fs @ fs', num)
    ([], [], num)
    es

let translate_fact ?(num = 0) namespace (f : Syntax.fact) =
  match f.Location.data with
  | Syntax.Fact (id, es) ->
      let es, fs, num = translate_expr2s ~num es in
      Fact (id, namespace, es), fs, [], num
  | Syntax.GlobalFact (id, es) ->
      let es, fs, num = translate_expr2s ~num es in
      GlobalFact (id, es), fs, [], num
  | Syntax.ChannelFact (ch, id, es) ->
      let es, fs, num = translate_expr2s ~num es in
      let e, fs', num = translate_expr2 ~num ch in
      ChannelFact (id, e, es), fs @ fs', [ e ], num
  | Syntax.EqFact (e1, e2) ->
      let es, fs, num = translate_expr2s ~num [ e1; e2 ] in
      let e1, e2 =
        match es with
        | [ e1; e2 ] -> e1, e2
        | _ -> assert false
      in
      EqFact (e1, e2), fs, [], num
  | Syntax.NeqFact (e1, e2) ->
      let es, fs, num = translate_expr2s ~num [ e1; e2 ] in
      let e1, e2 =
        match es with
        | [ e1; e2 ] -> e1, e2
        | _ -> assert false
      in
      NeqFact (e1, e2), fs, [], num
  | Syntax.FileFact (p, d) ->
      let p, fs1, num = translate_expr2 ~num p in
      let d, fs2, num = translate_expr2 ~num d in
      FileFact (namespace, p, d), fs1 @ fs2, [ p ], num
  | Syntax.ProcessFact _ -> assert false
;;

let translate_facts ?(num = 0) namespace (fs : Syntax.fact list) =
  List.fold_left
    (fun (fs, gfs, es, num) f ->
       let f, gfs', es', num = translate_fact ~num namespace f in
       fs @ [ f ], gfs @ gfs', es @ es', num)
    ([], [], [], num)
    fs
;;

let rec expr_shift_meta shift e =
  let e' =
    match e.Location.data with
    | Syntax.Variable (v, Meta i) -> Syntax.Variable (v, Meta (i + shift))
    | Syntax.Apply (o, el) -> Syntax.Apply (o, List.map (expr_shift_meta shift) el)
    | Syntax.Tuple el -> Syntax.Tuple (List.map (expr_shift_meta shift) el)
    | _ -> e.Location.data
  in
  { e with data = e' }
;;

let _fact_shift_meta shift f =
  match f.Location.data with
  | Syntax.Fact (id, el) -> Syntax.Fact (id, List.map (expr_shift_meta shift) el)
  | Syntax.GlobalFact (id, el) ->
      Syntax.GlobalFact (id, List.map (expr_shift_meta shift) el)
  | Syntax.ChannelFact (ch, id, el) ->
      Syntax.ChannelFact
        (expr_shift_meta shift ch, id, List.map (expr_shift_meta shift) el)
  (* | Syntax.PathFact (path, id, el) ->
    Syntax.PathFact(expr_shift_meta shift path, id, (List.map (expr_shift_meta shift) el)) *)
  | Syntax.EqFact (e1, e2) ->
      Syntax.EqFact (expr_shift_meta shift e1, expr_shift_meta shift e2)
  | Syntax.NeqFact (e1, e2) ->
      Syntax.NeqFact (expr_shift_meta shift e1, expr_shift_meta shift e2)
  | Syntax.FileFact (e1, e2) ->
      Syntax.FileFact (expr_shift_meta shift e1, expr_shift_meta shift e2)
  | _ -> assert false
;;

let rec tamarin_expr_shift_meta shift e =
  match e with
  | MetaVar i -> MetaVar (i + shift)
  | Apply (s, el) -> Apply (s, List.map (tamarin_expr_shift_meta shift) el)
  | List el -> List (List.map (tamarin_expr_shift_meta shift) el)
  | _ -> e
;;

(* xxx not used *)
let _ = tamarin_expr_shift_meta

(*
   given a model, the current state that is promised to be already in the model,
  this function returns an extended model
*)
let rec translate_cmd mo (st : state) funs syscalls attacks scope syscall pol c =
  let return_var = get_return_var () in
  match c.Location.data with
  | Syntax.Return e ->
      let e, pre, _ = translate_expr2 e in
      let (st_f : state) = next_state st scope in
      let mo = add_state mo st_f in
      let mo =
        add_transition
          mo
          { transition_id = List.length mo.model_transitions
          ; transition_namespace = mo.model_name
          ; transition_name = "return"
          ; transition_from = st
          ; transition_to = st_f
          ; transition_pre = pre
          ; transition_post = []
          ; transition_state_transition =
              mk_state_transition_from_action (ActionReturn e) st.state_vars
          ; transition_label = []
          ; transition_is_loop_back = false
          }
      in
      mo, st_f
  | Syntax.Skip ->
      let st_f = next_state st scope in
      let mo = add_state mo st_f in
      let mo =
        add_transition
          mo
          { transition_id = List.length mo.model_transitions
          ; transition_namespace = mo.model_name
          ; transition_name = "skip"
          ; transition_from = st
          ; transition_to = st_f
          ; transition_pre = []
          ; transition_post = []
          ; transition_state_transition =
              mk_state_transition_from_action (ActionReturn Unit) st.state_vars
          ; transition_label = []
          ; transition_is_loop_back = false
          }
      in
      mo, st_f
  | Syntax.Sequence (c1, c2) ->
      let mo, st = translate_cmd mo st funs syscalls attacks scope syscall pol c1 in
      let mo, st = translate_cmd mo st funs syscalls attacks None syscall pol c2 in
      mo, st
  | Syntax.Put fl ->
      let post, pre, es, _ = translate_facts mo.model_name fl in
      let pre' =
        List.map (fun target -> AccessFact (mo.model_name, Param, target, syscall)) es
      in
      let st_f = next_state st scope in
      let mo = add_state mo st_f in
      let mo =
        add_transition
          mo
          { transition_id = List.length mo.model_transitions
          ; transition_namespace = mo.model_name
          ; transition_name = "put"
          ; transition_from = st
          ; transition_to = st_f
          ; transition_pre = pre @ pre'
          ; transition_post = post
          ; transition_state_transition =
              mk_state_transition_from_action (ActionReturn Unit) st.state_vars
          ; transition_label = []
          ; transition_is_loop_back = false
          }
      in
      mo, st_f
  | Syntax.Let (_v, e, c) ->
      let e, pre, _ = translate_expr2 e in
      let st_f = next_state ~shift_loc:1 st scope in
      let mo = add_state mo st_f in
      let mo =
        add_transition
          mo
          { transition_id = List.length mo.model_transitions
          ; transition_namespace = mo.model_name
          ; transition_name = "let_intro"
          ; transition_from = st
          ; transition_to = st_f
          ; transition_pre = pre
          ; transition_post = []
          ; transition_state_transition =
              mk_state_transition_from_action (ActionIntro [ e ]) st.state_vars
          ; transition_label = []
          ; transition_is_loop_back = false
          }
      in
      let mo, st = translate_cmd mo st_f funs syscalls attacks None syscall pol c in
      let st_f = next_state ~shift_loc:(-1) st scope in
      let mo = add_state mo st_f in
      let mo =
        add_transition
          mo
          { transition_id = List.length mo.model_transitions
          ; transition_namespace = mo.model_name
          ; transition_name = "let_out"
          ; transition_from = st
          ; transition_to = st_f
          ; transition_pre = []
          ; transition_post = []
          ; transition_state_transition =
              mk_state_transition_from_action (ActionPopLoc 1) st.state_vars
          ; transition_label = []
          ; transition_is_loop_back = false
          }
      in
      mo, st_f
  | Syntax.Assign ((_v, di), e) ->
      let e, pre, _ = translate_expr2 e in
      let st_f = next_state st scope in
      let mo = add_state mo st_f in
      let mo =
        add_transition
          mo
          { transition_id = List.length mo.model_transitions
          ; transition_namespace = mo.model_name
          ; transition_name = "assign"
          ; transition_from = st
          ; transition_to = st_f
          ; transition_pre = pre
          ; transition_post = []
          ; transition_state_transition =
              mk_state_transition_from_action (ActionAssign (di, e)) st.state_vars
          ; transition_label = []
          ; transition_is_loop_back = false
          }
      in
      mo, st_f
  | Syntax.FCall (ov, f, es) ->
      let rev_es, pre, _ = translate_expr2s ~num:0 es in
      let es = List.rev rev_es in
      let _f, _args, cmd = List.find (fun (f', _args, _cmd) -> f = f') funs in
      let st_f = next_state ~shift_loc:(List.length es) st scope in
      let mo = add_state mo st_f in
      let mo =
        add_transition
          mo
          { transition_id = List.length mo.model_transitions
          ; transition_namespace = mo.model_name
          ; transition_name = "fcall_intro"
          ; transition_from = st
          ; transition_to = st_f
          ; transition_pre = pre
          ; transition_post = []
          ; transition_state_transition =
              mk_state_transition_from_action (ActionIntro es) st.state_vars
          ; transition_label = []
          ; transition_is_loop_back = false
          }
      in
      let mo, st = translate_cmd mo st_f funs syscalls attacks None syscall pol cmd in
      let st_f =
        next_state ~shift_loc:(-List.length es) st scope
      in
      let mo = add_state mo st_f in
      let mo =
        add_transition
          mo
          { transition_id = List.length mo.model_transitions
          ; transition_namespace = mo.model_name
          ; transition_name = "fcall_out"
          ; transition_from = st
          ; transition_to = st_f
          ; transition_pre = []
          ; transition_post = []
          ; transition_state_transition =
              mk_state_transition_from_action
                (match ov with
                 | None -> ActionPopLoc (List.length es)
                 | Some (_, v) ->
                     ActionSeq
                       (ActionPopLoc (List.length es), ActionAssign (v, return_var)))
                st.state_vars
          ; transition_label = []
          ; transition_is_loop_back = false
          }
      in
      mo, st_f
  | Syntax.SCall (ov, o, es) ->
      let rev_es, pre, _ = translate_expr2s ~num:0 es in
      let es = List.rev rev_es in
      let _f, _args, cmd = List.find (fun (f', _args, _cmd) -> o = f') syscalls in
      let st_i =
        next_state ~shift_loc:(List.length es) st (Some [ 0 ])
      in
      let mo = add_state mo st_i in
      let mo =
        add_transition
          mo
          { transition_id = List.length mo.model_transitions
          ; transition_namespace = mo.model_name
          ; transition_name = "scall_intro"
          ; transition_from = st
          ; transition_to = st_i
          ; transition_pre = pre
          ; transition_post = []
          ; transition_state_transition =
              mk_state_transition_from_action (ActionIntro es) st.state_vars
          ; transition_label = []
          ; transition_is_loop_back = false
          }
      in
      let mo, st_m = translate_cmd mo st_i funs syscalls attacks None o pol cmd in
      let st_f = next_state st None in
      let mo = add_state mo st_f in
      let mo =
        add_transition
          mo
          { transition_id = List.length mo.model_transitions
          ; transition_namespace = mo.model_name
          ; transition_name = "scall_out"
          ; transition_from = st_m
          ; transition_to = st_f
          ; transition_pre = []
          ; transition_post = []
          ; transition_state_transition =
              mk_state_transition_from_action
                (match ov with
                 | None -> ActionPopLoc (List.length es)
                 | Some (_, v) ->
                     ActionSeq
                       (ActionPopLoc (List.length es), ActionAssign (v, return_var)))
                st_m.state_vars
          ; transition_label = []
          ; transition_is_loop_back = false
          }
      in
      (* if this system call is attacked *)
      (match
         List.find_all
           (fun (a, t, _, _cmd) ->
              t = o
              && List.exists
                   (fun (s1, s2) -> s1 = mo.model_type && s2 = a)
                   pol.Context.pol_attack)
           attacks
       with
       | [] -> mo, st_f
       | lst ->
           let scope_lst =
             List.map (fun i -> Some [ i + 1 ]) (List.init (List.length lst) (fun i -> i))
           in
           let mo =
             List.fold_left2
               (fun mo scope (_a, _, _, c) ->
                  let st_i2 =
                    next_state ~shift_loc:(List.length es) st scope
                  in
                  let mo = add_state mo st_i2 in
                  let mo =
                    add_transition
                      mo
                      { transition_id = List.length mo.model_transitions
                      ; transition_namespace = mo.model_name
                      ; transition_name = "attack_intro"
                      ; transition_from = st
                      ; transition_to = st_i2
                      ; transition_pre = pre
                      ; transition_post = []
                      ; transition_state_transition =
                          mk_state_transition_from_action (ActionIntro es) st.state_vars
                      ; transition_label = []
                      ; transition_is_loop_back = false
                      }
                  in
                  let mo, st_m =
                    translate_cmd mo st_i2 funs syscalls attacks None o pol c
                  in
                  add_transition
                    mo
                    { transition_id = List.length mo.model_transitions
                    ; transition_namespace = mo.model_name
                    ; transition_name = "attack_out"
                    ; transition_from = st_m
                    ; transition_to = st_f
                    ; transition_pre = []
                    ; transition_post = []
                    ; transition_state_transition =
                        mk_state_transition_from_action
                          (match ov with
                           | None -> ActionPopLoc (List.length es)
                           | Some (_, v) ->
                               ActionSeq
                                 ( ActionPopLoc (List.length es)
                                 , ActionAssign (v, return_var) ))
                          st_m.state_vars
                    ; transition_label = []
                    ; transition_is_loop_back = false
                    })
               mo
               scope_lst
               lst
           in
           mo, st_f)
  | Syntax.Case cs ->
      let scope_lst =
        match scope with
        | None -> List.map (fun i -> Some [ i ]) (List.init (List.length cs) (fun i -> i))
        | Some l ->
            List.map (fun i -> Some (i :: l)) (List.init (List.length cs) (fun i -> i))
      in
      (* final state for all branches *)
      let st_f = next_state st None in
      let mo =
        List.fold_left2
          (fun mo scope (vl, fl, c) ->
             let mo, st =
               translate_guarded_cmd
                 mo
                 st
                 funs
                 syscalls
                 attacks
                 scope
                 syscall
                 pol
                 (vl, fl, c)
             in
             add_transition
               mo
               { transition_id = List.length mo.model_transitions
               ; transition_namespace = mo.model_name
               ; transition_name = "case_out"
               ; transition_from = st
               ; transition_to = st_f
               ; transition_pre = []
               ; transition_post = []
               ; transition_state_transition =
                   mk_state_transition_from_action
                     (ActionPopMeta (List.length vl))
                     st.state_vars
               ; transition_label = []
               ; transition_is_loop_back = false
               })
          mo
          scope_lst
          cs
      in
      add_state mo st_f, st_f
  | Syntax.While (cs1, cs2) ->
      let mindex = st.state_index in
      let st_i = next_state st scope in
      let tid = List.length mo.model_transitions in
      let mo =
        add_transition
          mo
          { transition_id = tid
          ; transition_namespace = mo.model_name
          ; transition_name = "repeat_in"
          ; transition_from = st
          ; transition_to = st_i
          ; transition_pre = []
          ; transition_post = []
          ; transition_state_transition =
              mk_state_transition_from_action (ActionReturn Unit) st.state_vars
          ; transition_label = [ LoopFact (mo.model_name, mindex, 0) ]
          ; transition_is_loop_back = false
          }
      in
      let st = st_i in
      let scope_lst1 =
        List.map (fun i -> Some [ i ]) (List.init (List.length cs1) (fun i -> i))
      in
      let scope_lst2 =
        List.map
          (fun i -> Some [ i ])
          (List.init (List.length cs2) (fun i -> i + List.length cs1))
      in
      let st_f = next_state st None in
      let mo =
        (* xxx probably a dupe of Case *)
        List.fold_left2
          (fun mo scope (vl, fl, c) ->
             let mo, st_f =
               translate_guarded_cmd
                 mo
                 st
                 funs
                 syscalls
                 attacks
                 scope
                 syscall
                 pol
                 (vl, fl, c)
             in
             add_transition
               mo
               { transition_id = List.length mo.model_transitions
               ; transition_namespace = mo.model_name
               ; transition_name = "repeat"
               ; transition_from = st_f
               ; transition_to = st
               ; transition_pre = []
               ; transition_post = []
               ; transition_state_transition =
                   mk_state_transition_from_action
                     (ActionPopMeta (List.length vl))
                     st_f.state_vars
               ; transition_label = [ LoopFact (mo.model_name, mindex, 1) ]
               ; transition_is_loop_back = true
               })
          mo
          scope_lst1
          cs1
      in
      let mo =
        (* xxx probably a dupe of Case *)
        List.fold_left2
          (fun mo scope (vl, fl, c) ->
             let mo, st =
               translate_guarded_cmd
                 mo
                 st
                 funs
                 syscalls
                 attacks
                 scope
                 syscall
                 pol
                 (vl, fl, c)
             in
             add_transition
               mo
               { transition_id = List.length mo.model_transitions
               ; transition_namespace = mo.model_name
               ; transition_name = "repeat_out"
               ; transition_from = st
               ; transition_to = st_f
               ; transition_pre = []
               ; transition_post = []
               ; transition_state_transition =
                   mk_state_transition_from_action
                     (ActionPopMeta (List.length vl))
                     st.state_vars
               ; transition_label = [ LoopFact (mo.model_name, mindex, 2) ]
               ; transition_is_loop_back = false
               })
          mo
          scope_lst2
          cs2
      in
      add_state mo st_f, st_f
  | Syntax.Event fs ->
      let label, pre, _acps, _ = translate_facts mo.model_name fs in
      let st_f = next_state st scope in
      let mo = add_state mo st_f in
      let mo =
        add_transition
          mo
          { transition_id = List.length mo.model_transitions
          ; transition_namespace = mo.model_name
          ; transition_name = "event"
          ; transition_from = st
          ; transition_to = st_f
          ; transition_pre = pre
          ; transition_post = []
          ; transition_state_transition =
              mk_state_transition_from_action (ActionReturn Unit) st.state_vars
          ; transition_label = label
          ; transition_is_loop_back = false
          }
      in
      mo, st_f
  | Syntax.New (_v, fid_el_opt, c) ->
      let fid, el = Option.value fid_el_opt ~default:("", []) in
      let el, pre, _ = translate_expr2s ~num:0 el in
      let st_f = next_state ~shift_meta:1 st scope in
      let mo = add_state mo st_f in
      let mo =
        add_transition
          mo
          { transition_id = List.length mo.model_transitions
          ; transition_namespace = mo.model_name
          ; transition_name = "new_intro"
          ; transition_from = st
          ; transition_to = st_f
          ; transition_pre = FreshFact (MetaNewVar 0) :: pre
          ; transition_post =
              (if fid = ""
               then []
               else [ InjectiveFact (fid, mo.model_name, MetaNewVar 0, List el) ])
          ; transition_state_transition =
              mk_state_transition_from_action (ActionAddMeta 1) st.state_vars
          ; transition_label = []
          ; transition_is_loop_back = false
          }
      in
      let mo, st = translate_cmd mo st_f funs syscalls attacks None syscall pol c in
      let st_f = next_state ~shift_meta:(-1) st scope in
      let mo = add_state mo st_f in
      let mo =
        add_transition
          mo
          { transition_id = List.length mo.model_transitions
          ; transition_namespace = mo.model_name
          ; transition_name = "new_out"
          ; transition_from = st
          ; transition_to = st_f
          ; transition_pre = []
          ; transition_post = []
          ; transition_state_transition =
              mk_state_transition_from_action (ActionPopMeta 1) st.state_vars
          ; transition_label = []
          ; transition_is_loop_back = false
          }
      in
      mo, st_f
  | Syntax.Get (vl, id, fid, c) ->
      let e, pre, _ = translate_expr2 id in
      let st_f = next_state ~shift_meta:(List.length vl) st scope in
      let mo = add_state mo st_f in
      let mo =
        add_transition
          mo
          { transition_id = List.length mo.model_transitions
          ; transition_namespace = mo.model_name
          ; transition_name = "get_intro"
          ; transition_from = st
          ; transition_to = st_f
          ; transition_pre =
              [ InjectiveFact
                  ( fid
                  , mo.model_name
                  , e
                  , List (List.map (fun i -> MetaNewVar i) (int_to_list (List.length vl)))
                  )
              ]
              @ pre
          ; transition_post =
              [ InjectiveFact
                  ( fid
                  , mo.model_name
                  , e
                  , List (List.map (fun i -> MetaNewVar i) (int_to_list (List.length vl)))
                  )
              ]
          ; transition_state_transition =
              mk_state_transition_from_action
                (ActionAddMeta (List.length vl))
                st.state_vars
          ; transition_label = []
          ; transition_is_loop_back = false
          }
      in
      let mo, st = translate_cmd mo st_f funs syscalls attacks None syscall pol c in
      let st_f =
        next_state ~shift_meta:(-List.length vl) st scope
      in
      let mo = add_state mo st_f in
      let mo =
        add_transition
          mo
          { transition_id = List.length mo.model_transitions
          ; transition_namespace = mo.model_name
          ; transition_name = "get_out"
          ; transition_from = st
          ; transition_to = st_f
          ; transition_pre = []
          ; transition_post = []
          ; transition_state_transition =
              mk_state_transition_from_action
                (ActionPopMeta (List.length vl))
                st.state_vars
          ; transition_label = []
          ; transition_is_loop_back = false
          }
      in
      mo, st_f
  | Syntax.Del (id, fid) ->
      let e, pre, _ = translate_expr2 id in
      let st_f = next_state st scope in
      let mo = add_state mo st_f in
      let mo =
        add_transition
          mo
          { transition_id = List.length mo.model_transitions
          ; transition_namespace = mo.model_name
          ; transition_name = "del"
          ; transition_from = st
          ; transition_to = st_f
          ; transition_pre = [ InjectiveFact (fid, mo.model_name, e, MetaNewVar 0) ] @ pre
          ; transition_post = []
          ; transition_state_transition =
              mk_state_transition_from_action (ActionReturn Unit) st.state_vars
          ; transition_label = []
          ; transition_is_loop_back = false
          }
      in
      mo, st_f

and translate_guarded_cmd mo st funs syscalls attacks scope syscall pol (vl, fl, c) =
  let fl, gv, acps, _ = translate_facts mo.model_name fl in
  let acps =
    List.map (fun target -> AccessFact (mo.model_name, Param, target, syscall)) acps
  in
  let st_f = next_state ~shift_meta:(List.length vl) st scope in
  let mo = add_state mo st_f in
  (* let eng_f = engine_index_inc eng scope in *)
  let mo =
    add_transition
      mo
      { transition_id = List.length mo.model_transitions
      ; transition_namespace = mo.model_name
      ; transition_name = "guarded"
      ; transition_from = st
      ; transition_to = st_f
      ; transition_pre = fl @ gv @ acps
      ; transition_post = []
      ; transition_state_transition =
          mk_state_transition_from_action (ActionAddMeta (List.length vl)) st.state_vars
      ; transition_label = []
      ; transition_is_loop_back = false
      }
  in
  translate_cmd mo st_f funs syscalls attacks None syscall pol c


let translate_process
      { Context.proc_pid = k
      ; Context.proc_name = s
      ; Context.proc_type = pty_unused
      ; Context.proc_filesys = fls
      ; Context.proc_variable = vars
      ; Context.proc_function = fns
      ; Context.proc_main = m
      ; Context.proc_channels = _channels
      }
      syscalls
      attacks
      pol
  =
  let namespace = String.capitalize_ascii (s ^ if k = 0 then "" else string_of_int k) in
  (* this must be unique *)
  (* let t = add_comment t ("- Process name: " ^ namespace) in  *)
  let mo = initial_model ~namespace ~typ:pty_unused in
  let st = mo.model_init_state in
  (* installed channels: *)
  (* let (mo, st) = List.fold_left (fun (mo, st) c ->

  ) (mo, st) channels in *)

  (* initialize file system *)
  let mo, st =
    List.fold_left
      (fun (mo, st) (path, ty, e) ->
         (* let path = (mk_dir eng fsys path) in *)
         let st_f = next_state st None in
         let mo = add_state mo st_f in
         let e, gv, _ = translate_expr2 e in
         let path, _gv', _ = translate_expr2 path in
         (* let name = mk_fact_name  namespace^ replace_string '/' !separator path in  *)
         let mo =
           add_transition
             mo
             { transition_id = List.length mo.model_transitions
             ; transition_namespace = mo.model_name
             ; transition_name = "init_filesys"
             ; transition_from = st
             ; transition_to = st_f
             ; transition_pre = gv
             ; transition_post =
                 ([ FileFact (namespace, path, e) ]
                  @ List.map
                      (fun (_, _, scall) ->
                         AccessFact (mo.model_name, Param, path, scall))
                      (List.filter
                         (fun (pty, tyl, _) ->
                            pty = pty_unused && List.exists (fun s -> s = ty) tyl)
                         pol.Context.pol_access)
                  @
                  if
                    List.exists
                      (fun (pty, tyl) ->
                         pty = pty_unused && List.exists (fun s -> s = ty) tyl)
                      pol.Context.pol_access_all
                  then [ AccessFact (mo.model_name, Param, path, "") ]
                  else [])
             ; transition_state_transition =
                 mk_state_transition_from_action (ActionReturn Unit) st.state_vars
             ; transition_label = []
             ; transition_is_loop_back = false
             }
         in
         mo, st_f)
      (mo, st)
      fls
  in
  (* initialize rule *)
  (* let mo = add_rule mo (name, "",
  [],
  [InitFact([String namespace; String path])],
  [FileFact(namespace, path, e)]) in *)

  (* initialize memory *)
  let mo, st =
    List.fold_left
      (fun (mo, st) (_x, e) ->
         let st_f = next_state ~shift_top:1 st None in
         let mo = add_state mo st_f in
         let e, gv, _ = translate_expr2 e in
         let mo =
           add_transition
             mo
             { transition_id = List.length mo.model_transitions
             ; transition_namespace = mo.model_name
             ; transition_name = "init_mem"
             ; transition_from = st
             ; transition_to = st_f
             ; transition_pre = gv
             ; transition_post = []
             ; transition_state_transition =
                 mk_state_transition_from_action (ActionLetTop [ e ]) st.state_vars
             ; transition_label = []
             ; transition_is_loop_back = false
             }
         in
         mo, st_f)
      (mo, st)
      (List.rev vars)
  in
  (* translate the main function *)
  let mo, _st = translate_cmd mo st fns syscalls attacks None "" pol m in
  mo
;;

let get_fact_names ctx =
  List.map (fun (a, _, _) -> a) ctx.Context.ctx_fact
  @ List.map fst ctx.Context.ctx_event
  @ List.map fst ctx.Context.ctx_ext_syscall
  @ List.fold_left
      (fun l proc ->
         [ proc.Context.ctx_proctmpl_id ]
         @ List.map fst proc.Context.ctx_proctmpl_func
         @ l)
      []
      ctx.Context.ctx_proctmpl
;;

let translate_sys
      { Context.sys_ctx = ctx
      ; Context.sys_def = def
      ; Context.sys_pol = pol
      ; Context.sys_proc = proc
      ; Context.sys_param_proc = param_proc
      ; Context.sys_lemma = lem
      }
      (used_idents, used_string)
  =
  (separator
   := let names = get_fact_names ctx in
      let rec f s =
        if List.exists (fun u -> contains u s) names then f (s ^ "_") else s
      in
      f "_");
  (fresh_ident
   := let rec f s = if List.exists (fun u -> u = s) used_idents then f (s ^ "_") else s in
      f "rab");
  (fresh_string
   := let rec f s = if List.exists (fun u -> u = s) used_string then f (s ^ "_") else s in
      f "rab");
  (fresh_param
   := let rec f s = if List.exists (fun u -> u = s) used_string then f (s ^ "_") else s in
      f "param");
  let sep = !separator in
  let t : tamarin = empty_tamarin in
  (* process signature *)
  let t =
    List.fold_left
      (fun t (f, arity) -> add_fun t (f, arity))
      t
      (List.rev ctx.Context.ctx_ext_func)
  in
  let t =
    List.fold_left (fun t c -> add_const t c) t (List.rev ctx.Context.ctx_ext_const)
  in
  let t =
    List.fold_left
      (fun t (_, e1, e2) -> add_eqn t (translate_expr e1, translate_expr e2))
      t
      (List.rev def.Context.def_ext_eq)
  in
  (* global constants *)
  let t = add_comment t "Global Constants:" in
  let t =
    List.fold_left
      (fun t (v, e) ->
         match e with
         | None ->
             (* when v is fresh *)
             add_rule
               t
               { name = "Const" ^ sep ^ v
               ; role = ""
               ; pre = [ FreshFact' (Var v) ]
               ; label =
                   [ InitFact [ String ("Const" ^ sep ^ v) ]
                   ; InitFact [ List [ String ("Const" ^ sep ^ v); Var v ] ]
                   ; mk_constant_fact v
                   ]
               ; post = [ mk_constant_fact v ]
               }
         | Some e ->
             (* when v is defined *)
             let e, gv, _ = translate_expr2 e in
             add_rule
               t
               { name = "Const" ^ sep ^ v
               ; role = ""
               ; pre = gv
               ; label = [ ConstantFact (String v, e) ]
               ; post = [ ConstantFact (String v, e) ]
               })
      t
      (List.rev def.Context.def_const)
  in
  let t = add_comment t "Parametric global Constants:" in
  let t =
    List.fold_left
      (fun t (v, e) ->
         match e with
         | None ->
             (* when v is fresh *)
             add_rule
               t
               { name = "Const" ^ sep ^ v
               ; role = ""
               ; pre = [ FreshFact' (Var v) ]
               ; label =
                   [ InitFact [ expr_pair (String v) Param ]
                   ; ConstantFact (expr_pair (String v) Param, Var v)
                   ]
               ; post = [ ConstantFact (expr_pair (String v) Param, Var v) ]
               }
         | Some (_p, e) ->
             (* when v is defined *)
             let e, gv, _ = translate_expr2 e in
             add_rule
               t
               { name = "Const" ^ sep ^ v
               ; role = ""
               ; pre = gv
               ; label =
                   [ InitFact [ expr_pair (String v) Param ]
                   ; ConstantFact (expr_pair (String v) Param, e)
                   ]
               ; post = [ ConstantFact (expr_pair (String v) Param, e) ]
               })
      t
      (List.rev def.Context.def_param_const)
  in
  let t = add_comment t "Access control:" in
  (* access control *)
  (* let t = add_comment t "Processes:" in *)
  let mos =
    List.fold_left
      (fun mos p ->
         translate_process p def.Context.def_ext_syscall def.Context.def_ext_attack pol
         :: mos)
      []
      (List.rev proc)
  in
  let facts_gv_list : (bool * fact list * fact list) list =
    List.fold_left
      (fun facts_gv_list p ->
         let namespace =
           String.capitalize_ascii
             (p.Context.proc_name
              ^ if p.Context.proc_pid = 0 then "" else string_of_int p.Context.proc_pid)
         in
         let new_pol =
           pol.Context.pol_access
           @ List.map (fun (a, b) -> a, b, "") pol.Context.pol_access_all
         in
         let facts_gv_list' =
           List.fold_left
             (fun facts_gv_list c ->
                (* List.fold_left  *)
                (match c with
                 | Syntax.ChanArg { id = cname; typ = cty; param = None } ->
                     ( false
                     , List.map
                         (fun (_, _, scall) ->
                            AccessFact
                              (namespace, String !fresh_string, String cname, scall))
                         (List.filter
                            (fun (pty, tyl, _scall) ->
                               pty = p.Context.proc_type
                               && List.exists (fun v -> v = cty) tyl)
                            new_pol)
                     , [] )
                 | Syntax.ChanArg { id = cname; typ = cty; param = Some None } ->
                     ( true
                     , List.map
                         (fun (_, _, scall) ->
                            AccessFact
                              ( namespace
                              , String !fresh_string
                              , List [ String cname; Var !fresh_ident ]
                              , scall ))
                         (List.filter
                            (fun (pty, tyl, _scall) ->
                               pty = p.Context.proc_type
                               && List.exists (fun v -> v = cty) tyl)
                            new_pol)
                     , [] )
                 | Syntax.ChanArg { id = cname; typ = cty; param = Some (Some e) } ->
                     let e, gv', _ = translate_expr2 e in
                     ( false
                     , List.map
                         (fun (_, _, scall) ->
                            AccessFact
                              ( namespace
                              , String !fresh_string
                              , List [ String cname; e ]
                              , scall ))
                         (List.filter
                            (fun (pty, tyl, _scall) ->
                               pty = p.Context.proc_type
                               && List.exists (fun v -> v = cty) tyl)
                            new_pol)
                     , gv' ))
                :: facts_gv_list)
             []
             p.Context.proc_channels
         in
         facts_gv_list @ facts_gv_list')
      []
      (List.rev proc)
  in
  let t =
    add_rule
      t
      { name = "Init" ^ !separator ^ "system"
      ; role = "system"
      ; pre = []
      ; label = [ InitFact [ String "system" ] ]
      ; post =
          (* initializing tokens..  *)
          List.map
            (fun m ->
               let st = m.model_init_state in
               if !Config.tag_transition
               then
                 mk_state_fact
                   ~param:!fresh_string
                   st
                   empty_state_desc
                   (Some (mk_transition_expr `Initial))
               else mk_state_fact ~param:!fresh_string st empty_state_desc None)
            mos
          @ [ AccessGenFact ("system" ^ !separator, String !fresh_string) ]
      }
  in
  let t, _ =
    List.fold_left
      (fun (t, n) (b, (facts : fact list), gv) ->
         List.fold_left
           (fun (t, n) (fact : fact) ->
              ( add_rule
                  t
                  { name =
                      "Init"
                      ^ !separator
                      ^ "system"
                      ^ !separator
                      ^ "ACP"
                      ^ !separator
                      ^ string_of_int n
                  ; role = "system"
                  ; pre =
                      gv @ [ AccessGenFact ("system" ^ !separator, String !fresh_string) ]
                  ; label =
                      [ (if b
                         then
                           InitFact
                             [ List
                                 [ String
                                     ("system"
                                      ^ !separator
                                      ^ "ACP"
                                      ^ !separator
                                      ^ string_of_int n)
                                 ; Var !fresh_ident
                                 ]
                             ]
                         else
                           InitFact
                             [ String
                                 ("system"
                                  ^ !separator
                                  ^ "ACP"
                                  ^ !separator
                                  ^ string_of_int n)
                             ])
                      ]
                  ; post = [ fact ]
                  }
              , n + 1 ))
           (t, n)
           facts)
      (t, 0)
      facts_gv_list
  in
  let t = List.fold_left (fun t m -> add_model t m) t mos in
  let t, _ =
    List.fold_left
      (fun (t, n) pl ->
         let mos =
           List.fold_left
             (fun mos p ->
                translate_process
                  p
                  def.Context.def_ext_syscall
                  def.Context.def_ext_attack
                  pol
                :: mos)
             []
             (List.rev pl)
         in
         let facts_gv_list =
           List.fold_left
             (fun facts_gv_list p ->
                let namespace =
                  String.capitalize_ascii
                    (p.Context.proc_name
                     ^
                     if p.Context.proc_pid = 0
                     then ""
                     else string_of_int p.Context.proc_pid)
                in
                (* print_string namespace; *)
                let new_pol =
                  pol.Context.pol_access
                  @ List.map (fun (a, b) -> a, b, "") pol.Context.pol_access_all
                in
                let facts_gv_list' =
                  List.fold_left
                    (fun facts_gv_list c ->
                       (match c with
                        | Syntax.ChanArg { id = cname; typ = cty; param = None } ->
                            ( false
                            , List.map
                                (fun (_, _, scall) ->
                                   AccessFact (namespace, Param, String cname, scall))
                                (List.filter
                                   (fun (pty, tyl, _scall) ->
                                      pty = p.Context.proc_type
                                      && List.exists (fun v -> v = cty) tyl)
                                   new_pol)
                            , [] )
                        | Syntax.ChanArg { id = cname; typ = cty; param = Some None } ->
                            ( true
                            , List.map
                                (fun (_, _, scall) ->
                                   AccessFact
                                     ( namespace
                                     , Param
                                     , List [ String cname; Var !fresh_ident ]
                                     , scall ))
                                (List.filter
                                   (fun (pty, tyl, _scall) ->
                                      pty = p.Context.proc_type
                                      && List.exists (fun v -> v = cty) tyl)
                                   new_pol)
                            , [] )
                        | Syntax.ChanArg { id = cname; typ = cty; param = Some (Some e) }
                          ->
                            let e, gv', _ = translate_expr2 e in
                            ( false
                            , List.map
                                (fun (_, _, scall) ->
                                   AccessFact
                                     (namespace, Param, List [ String cname; e ], scall))
                                (List.filter
                                   (fun (pty, tyl, _scall) ->
                                      pty = p.Context.proc_type
                                      && List.exists (fun v -> v = cty) tyl)
                                   new_pol)
                            , gv' ))
                       :: facts_gv_list)
                    []
                    p.Context.proc_channels
                in
                facts_gv_list @ facts_gv_list')
             []
             (List.rev pl)
         in
         let t =
           add_rule
             t
             { name = "Init" ^ !separator ^ "system" ^ string_of_int n
             ; role = "system" ^ string_of_int n
             ; pre =
                 [ FreshFact' Param ]
                 (* XXX This produce the same compilation but not sure it is semantically correct *)
             ; label =
                 [ InitFact [ List [ String ("system" ^ string_of_int n); Param ] ] ]
             ; post =
                 [ AccessGenFact ("system" ^ string_of_int n ^ !separator, Param) ]
                 @ List.map
                     (fun m ->
                        let st = m.model_init_state in
                        if !Config.tag_transition
                        then
                          mk_state_fact
                            st
                            empty_state_desc
                            (Some (mk_transition_expr `Initial))
                        else mk_state_fact st empty_state_desc None)
                     mos
             }
         in
         let t, _ =
           List.fold_left
             (fun (t, m) (b, facts, gv) ->
                List.fold_left
                  (fun (t, m) (fact : fact) ->
                     ( add_rule
                         t
                         { name =
                             "Init"
                             ^ !separator
                             ^ "system"
                             ^ string_of_int n
                             ^ !separator
                             ^ "ACP"
                             ^ !separator
                             ^ string_of_int m
                         ; role = "system" ^ string_of_int n
                         ; pre =
                             gv
                             @ [ AccessGenFact
                                   ("system" ^ string_of_int n ^ !separator, Param)
                               ]
                         ; label =
                             [ (if b
                                then
                                  InitFact
                                    [ List
                                        [ String
                                            ("system"
                                             ^ string_of_int n
                                             ^ !separator
                                             ^ "ACP"
                                             ^ !separator
                                             ^ string_of_int m)
                                        ; Param
                                        ; Var !fresh_ident
                                        ]
                                    ]
                                else
                                  InitFact
                                    [ List
                                        [ String
                                            ("system"
                                             ^ string_of_int n
                                             ^ !separator
                                             ^ "ACP"
                                             ^ !separator
                                             ^ string_of_int m)
                                        ; Param
                                        ]
                                    ])
                             ]
                         ; post = [ fact ]
                         }
                     , m + 1 ))
                  (t, m)
                  facts)
             (t, 0)
             facts_gv_list
         in
         let t = List.fold_left (fun t m -> add_model t m) t mos in
         t, n + 1)
      (t, 1)
      (List.rev param_proc)
  in
  (* translating lemmas now *)
  let t =
    List.fold_left
      (fun t l ->
         let l =
           match l.Location.data with
           | Syntax.PlainLemma { name=l; desc= p } -> PlainLemma (l, p)
           | Syntax.ReachabilityLemma { name= l; facts= fs; _ } ->
               let fs, gv, _, _ = translate_facts "" fs in
               ReachabilityLemma (l, gv, fs)
           | Syntax.CorrespondenceLemma {name= l; fresh_variables= vl; premise= a; conclusion= b } ->
               let a, gva =
                 match translate_facts "" [ a ] with
                 | [ a ], gva, _, _ -> a, gva
                 | _ -> assert false
               in
               let b, gvb =
                 match translate_facts "" [ b ] with
                 | [ b ], gvb, _, _ -> b, gvb
                 | _ -> assert false
               in
               CorrespondenceLemma (l, vl, (gva, a), (gvb, b))
           (* | Syntax.CorrespondenceLemma (l, vars, e1, e2) ->
        CorrespondenceLemma (l, vars,
            (match e1.Location.data with
            | Syntax.Event (id, el) -> (mk_fact_name id, List.map (translate_expr ~ch:false) el)),
            (match e2.Location.data with
            | Syntax.Event (id, el) -> (mk_fact_name id, List.map (translate_expr ~ch:false) el)))
           *)
         in
         add_lemma t l)
      t
      lem
  in
  t
;;
