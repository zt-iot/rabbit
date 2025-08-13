

(* reads whether lvl_a is less than or equal to lvl_b *)
let leq_secrecy (secrecy_lattice : cst_access_policy) (lvl_a : Cst_syntax.secrecy_lvl) (lvl_b : Cst_syntax.secrecy_lvl) = 
  match lvl_a, lvl_b with 
  (* Public is smaller than every secrecy lvl *)
  | Cst_syntax.Public, _ -> true 
  | Cst_syntax.SNode(a_set), Cst_syntax.SNode(b_set) -> 
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


(* reads whether integrity lvl a is less than or equal to integrity lvl b *)
let leq_integrity (integrity_lattice : cst_access_policy) (lvl_a : Cst_syntax.integrity_lvl) (lvl_b : Cst_syntax.integrity_lvl) = 
  match lvl_a, lvl_b with 
  (* Every element is less than or equal to Untrusted *)
  | _, Cst_syntax.Untrusted -> true 


  | Cst_syntax.INode(a_set), Cst_syntax.INode(b_set) -> 
    let comparison, rel = integrity_lattice in 

    begin match rel with 
    | LessThanOrEqual -> 
      (List.assoc (a_set, b_set) comparison)
    | GreaterThanOrEqual -> 
      (raise (CstConversionException "cannot call leq_integrity on a secrecy lattice"))
    end
  | _, _ -> false







(* Determines whether security type t1 is a subtype of security type t2 (i.e. whether t1 <: t2) *)
let is_subtype (secrecy_lattice : cst_access_policy) (integrity_lattice : cst_access_policy) 
  (t1 : Cst_syntax.core_security_type) (t2 : Cst_syntax.core_security_type) (loc : Location.t) : bool = 
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