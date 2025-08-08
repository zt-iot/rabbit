open Sets


type relation = 
  | LessThanOrEqual
  | GreaterThanOrEqual


type cst_access_policy = ((proc_ty_set * proc_ty_set) * bool) list * relation


exception CstConversionException of string


let raise_conv_exception_with_location msg loc = 
    Location.print loc Format.std_formatter;
    Format.pp_print_newline Format.std_formatter ();
    raise (CstConversionException msg)




(* reads whether lvl_a is less than or equal to lvl_b *)
let leq_secrecy (secrecy_lattice : cst_access_policy) (lvl_a : Cst_env.secrecy_lvl) (lvl_b : Cst_env.secrecy_lvl) = 
  match lvl_a, lvl_b with 
  (* Public is smaller than every secrecy lvl *)
  | Cst_env.Public, _ -> true 
  | Cst_env.SNode(a_set), Cst_env.SNode(b_set) -> 
    let comparison, rel = secrecy_lattice in
    begin match rel with 
    | GreaterThanOrEqual -> 
      (* This is a sub-optimal way to compute, but for now we need it due to the way that secrecy_lattice is built *)
      let eq = ProcTySet.equal a_set b_set in 
      let a_set_geq_b_set = (List.assoc (a_set, b_set) comparison) in 
      (not a_set_geq_b_set) || eq
    | LessThanOrEqual -> (raise (CstConversionException "cannot call leq_secrecy on an integrity lattice"))
    end 
  | _, _ -> false 

(* reads whether lvl_a is greater than or equal to lvl_b
let geq_integrity (integrity_lattice : cst_access_policy) (lvl_a : Cst_env.integrity_lvl) (lvl_b : Cst_env.integrity_lvl) = 
  match lvl_a, lvl_b with 
  (* Untrusted is greater than every integrity lvl *)
  | Cst_env.Untrusted, _ -> true 
  | Cst_env.INode(a_set), Cst_env.INode(b_set) -> 
    let comparison, rel = integrity_lattice in 

    begin match rel with 
    | GreaterThanOrEqual -> List.assoc (a_set, b_set) comparison
    | LessThanOrEqual ->
      (raise (CstConversionException "cannot call geq_integrity on a secrecy lattice"))
    end
  | _, _ -> false *)


(* reads whether integrity lvl a is less than or equal to integrity lvl b *)
let leq_integrity (integrity_lattice : cst_access_policy) (lvl_a : Cst_env.integrity_lvl) (lvl_b : Cst_env.integrity_lvl) = 
  match lvl_a, lvl_b with 
  (* Every element is less than or equal to Untrusted *)
  | _, Cst_env.Untrusted -> true 


  | Cst_env.INode(a_set), Cst_env.INode(b_set) -> 
    let comparison, rel = integrity_lattice in 

    begin match rel with 
    | LessThanOrEqual -> 
      (List.assoc (a_set, b_set) comparison)
    | GreaterThanOrEqual -> 
      (raise (CstConversionException "cannot call leq_integrity on a secrecy lattice"))
    end
  | _, _ -> false



(* Whether two `core_security_type`'s hold the same data, ignoring any (secrecy_lvl * integrity_lvl) *)
let rec equals_datatype (ty1 : Cst_env.core_security_type) (ty2 : Cst_env.core_security_type) (loc : Location.t) : bool =
  let (ct1, _) = ty1 in
  let (ct2, _) = ty2 in
  match ct1, ct2 with
  | TUnit, TUnit -> true
  | Dummy, Dummy -> true
  | TChan lst1, TChan lst2 -> 
      let same_length = (List.length lst1 = List.length lst2) in 
      if not same_length then
        (raise_conv_exception_with_location "channels do not have the same amount of type parameters" loc);
      let same_typ_params = List.for_all2 (fun typ1 typ2 -> equals_datatype typ1 typ2 loc) lst1 lst2 in 
      same_length && same_typ_params
  | TSimple (id1, lst1), TSimple (id2, lst2) ->
      let same_type = Name.equal id1 id2 in 
      let same_length = (List.length lst1 = List.length lst2) in 
      if not same_length then
        (raise_conv_exception_with_location "simple types do not have the same amount of type parameters" loc);
      let same_typ_params = List.for_all2 (fun typ1 typ2 -> equals_datatype typ1 typ2 loc) lst1 lst2 in 
      same_type && same_length && same_typ_params
  | TProd (a1, b1), TProd (a2, b2) ->
      equals_datatype a1 a2 loc && equals_datatype b1 b2 loc
  | _, _ -> false



(* Determines whether security type t1 is a subtype of security type t2 (i.e. whether t1 <: t2) *)
let is_subtype (secrecy_lattice : cst_access_policy) (integrity_lattice : cst_access_policy) 
  (t1 : Cst_env.core_security_type) (t2 : Cst_env.core_security_type) (loc : Location.t) : bool = 
  (* for t1 to be a subtype of t2, it must hold that: 
    1.) t1 is of the same datatype as t2, and:
    2.) t1's secrecy level is smaller than or equal to the secrecy level of t2, and:
    3.) t1's integrity level is smaller than or equal to the integrity level of t2
  *)

  let (_, (t1_secrecy, t1_integrity)) = t1 in 
  let (_, (t2_secrecy, t2_integrity)) = t2 in 
  let same_datatype = equals_datatype t1 t2 loc in 
  let secrecy_cnd = begin match (t1, t2) with 
    (* For channel types, we currently do not care about secrecy levels *)
    | ((TChan _, _), (TChan _, _)) -> true 
    (* For the Dummy constructor, we do not care about secrecy levels *)
    | ((Dummy, _), (Dummy, _)) -> true
    | _ -> leq_secrecy secrecy_lattice t1_secrecy t2_secrecy 
  end in 
  let integrity_cnd = begin match (t1, t2) with 
    (* For channel types, we currently do not care about integrity levels *)
    | ((TChan _, _), (TChan _, _)) -> true 
    (* For the Dummy constructor, we do not care about integrity levels *)
    | ((Dummy, _), (Dummy, _)) -> true
    | _ -> leq_integrity integrity_lattice t1_integrity t2_integrity
  end in 
  same_datatype && secrecy_cnd && integrity_cnd





(* Given an `u : proc_ty_set`, return 'vs', a set of all `proc_ty_set`s such that for each v \in vs, v <= u *)
let elements_less_than_or_equal_to_u (pol : cst_access_policy) (u : proc_ty_set) : ProcTySetSet.t =
  if (snd pol) = LessThanOrEqual then   
    List.fold_left (fun acc ((v, u'), rel_holds) ->
      if ProcTySet.equal u u' && rel_holds then
        ProcTySetSet.add v acc
      else
        acc
    ) ProcTySetSet.empty (fst pol)
   else
    List.fold_left (fun acc ((u', v), rel_holds) ->
      if ProcTySet.equal u u' && rel_holds then
        ProcTySetSet.add v acc
      else
        acc
    ) ProcTySetSet.empty (fst pol)


(* Given an `a : proc_ty_set`, return bs, a set of all `proc_ty_set`s such that for each b \in bs, b >= a *)
let elements_greater_than_or_equal_to_u (pol : cst_access_policy) (u : proc_ty_set) : ProcTySetSet.t =
  if (snd pol) = GreaterThanOrEqual then   
    List.fold_left (fun acc ((v, u'), rel_holds) ->
      if ProcTySet.equal u u' && rel_holds then
        ProcTySetSet.add v acc
      else
        acc
    ) ProcTySetSet.empty (fst pol)
   else
    List.fold_left (fun acc ((u', v), rel_holds) ->
      if ProcTySet.equal u u' && rel_holds then
        ProcTySetSet.add v acc
      else
        acc
    ) ProcTySetSet.empty (fst pol)



    



(****
FUNCTIONS TO COMPUTE LEAST UPPER BOUND AND GREATEST LOWER BOUND
****)
let find_extremum_in_intersect
    ~(find_max : bool)
    (pol : cst_access_policy)
    (intersect : ProcTySetSet.t) : proc_ty_set option =

  let (rel, relation_kind) = pol in

  let rel_holds a b =
    List.exists (fun ((x, y), holds) ->
       ProcTySet.equal x a && ProcTySet.equal y b && holds
    ) rel
  in

  let is_extremum candidate =
    (* check if candidate is _relation_ for all `other \in intersect` *)
    ProcTySetSet.for_all (fun other ->
      (* the relation always holds on the candidate itself *)
      if ProcTySet.equal candidate other then true

      (* otherwise, check if `rel` holds depending on `relation_kind` *)
      else match (find_max, relation_kind) with
        | (true, LessThanOrEqual) -> rel_holds other candidate  (* other <= candidate <-> candidate is max *)
        | (false, LessThanOrEqual) -> rel_holds candidate other  (* candidate <= other <-> candidate is min *)
        | (true, GreaterThanOrEqual) -> rel_holds candidate other (* candidate >= other <-> candidate is max *)
        | (false, GreaterThanOrEqual) -> rel_holds other candidate (* other >= candidate <-> candidate is min *)
    ) intersect
  in

  let extremums = Seq.filter is_extremum (ProcTySetSet.to_seq intersect) in 
  let extremum_opt = Seq.uncons extremums in
  match extremum_opt with
  | Some (proc_ty_set, _) -> Some proc_ty_set
  | None -> None 


(* Given two secrecy levels a and b: 
- return the secrecy lvl which is the least upper bound of a and b, if it exists
- otherwise, return None
*)
let join_of_secrecy_lvls (pol : cst_access_policy) (a : Cst_env.secrecy_lvl) (b : Cst_env.secrecy_lvl) : Cst_env.secrecy_lvl option = 
  match (a, b) with
  | Cst_env.S_Ignore, _ -> None 
  | _, Cst_env.S_Ignore -> None 
  (* If one secrecy_lvl is Public, the least upper bound is the other secrecy_lvl *)
  | Cst_env.Public, _ -> Some b 
  | _, Cst_env.Public -> Some a 
  | Cst_env.SNode(a_set), Cst_env.SNode(b_set) -> 
    
    let elements_greater_than_a = elements_greater_than_or_equal_to_u pol a_set in 
    let elements_greater_than_b = elements_greater_than_or_equal_to_u pol b_set in 

    (* find the maximum element in the set of elements greater than both a and b *)
    let intersect = ProcTySetSet.inter elements_greater_than_a elements_greater_than_b in 
    let candidate = find_extremum_in_intersect ~find_max:true pol intersect in 

    match candidate with 
    | Some res -> Some (SNode res)
    | None -> None 
    

(* Given two integrity levels a and b:
- return the integrity lvl which is the greatest lower bound of a and b, if it exists
- otherwsie, return None
*)
let meet_of_integrity_lvls (pol : cst_access_policy) (a : Cst_env.integrity_lvl) (b : Cst_env.integrity_lvl) : Cst_env.integrity_lvl option = 
  match (a, b) with 
  | Cst_env.I_Ignore, _ -> None
  | _, Cst_env.I_Ignore -> None
  (* if one integrity_lvl is Untrusted, the greatest lower bound is the other integrity_lvl *)
  | Cst_env.Untrusted, _ -> Some b
  | _, Cst_env.Untrusted -> Some a 
  | Cst_env.INode(a_set), Cst_env.INode(b_set) -> 
    
    let elements_less_than_or_equal_to_a = elements_less_than_or_equal_to_u pol a_set in 
    let elements_less_than_or_equal_to_b = elements_less_than_or_equal_to_u pol b_set in 

    (* find the minimum element in the set of elements less than both a and b *)
    let intersect = ProcTySetSet.inter elements_less_than_or_equal_to_a elements_less_than_or_equal_to_b in 

    let candidate = find_extremum_in_intersect ~find_max:false pol intersect in 

    match candidate with 
    | Some (res) -> Some (INode res)
    | None -> None
(****
****)