(* Variant of the function unify_for_lemma of rules.ml.
   Maybe a bit cleaner but slower. Vincent's version is fine. *)


(* In this function, we instantiate in priority existential variables from lemma. *)
let rec unify_for_lemma priority_vars t1 t2 = match (t1,t2) with
    (Var v, Var v') when v == v' -> ()
  | (Var v, _) ->
      begin
        match v.link with
        | NoLink ->
            begin
              match t2 with
              | Var {link = TLink t2'} -> unify_for_lemma priority_vars t1 t2'
              | Var v' ->
		  if v.unfailing && not v'.unfailing then link v (TLink t2) else
		  if v'.unfailing && not v.unfailing then link v' (TLink t1) else
		  let vprio = List.memq v priority_vars in
		  let vprio' = List.memq v' priority_vars in
		  if vprio && not vprio' then link v (TLink t2) else
		  if vprio' && not vprio then link v' (TLink t1) else
		  if v'.vname.name = Param.def_var_name then link v' (TLink t1) else
		  link v (TLink t2)
              | FunApp (f_symb,_) when f_symb.f_cat = Failure && v.unfailing = false -> raise Unify
              | _ ->
                  occur_check v t2;
             	  link v (TLink t2)
            end
        | TLink t1' -> unify_for_lemma priority_vars t1' t2
        | _ -> internal_error "Unexpected link in unify 1"
      end
  | (FunApp(f_symb,_), Var v) ->
      begin
        match v.link with
          NoLink ->
            if v.unfailing = false && f_symb.f_cat = Failure
            then raise Unify
            else
              begin
             	occur_check v t1;
	        link v (TLink t1)
	      end
        | TLink t2' -> unify_for_lemma priority_vars t1 t2'
        | _ -> internal_error "Unexpected link in unify 2"
      end
  | (FunApp(f1, l1), FunApp(f2,l2)) ->
      if f1 != f2 then raise Unify;
      List.iter2 (unify_for_lemma priority_vars) l1 l2

