
open Sets


exception LatticeException of string


type secrecy_lvl = 
  | Public 
  | SNode of proc_ty_set
[@@deriving eq]


type integrity_lvl = 
  | Untrusted
  | INode of proc_ty_set
[@@deriving eq]

(* convert from all process types to 'Public' *)
let proc_ty_set_to_secrecy_lvl readers all_process_typs = 
  if readers = all_process_typs then 
    Public 
  else
    SNode readers  

(* convert from all process types to 'Untrusted'*)
let proc_ty_set_to_integrity_lvl providers all_process_typs = 
  if providers = all_process_typs then
    Untrusted
  else 
    INode providers

type relation = 
  | LessThanOrEqual
  | GreaterThanOrEqual


type cst_access_policy = ((proc_ty_set * proc_ty_set) * bool) list * relation



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
let join_of_secrecy_lvls (pol : cst_access_policy) (a : secrecy_lvl) (b : secrecy_lvl) : secrecy_lvl option = 
  match (a, b) with
  (* If one secrecy_lvl is Public, the least upper bound is the other secrecy_lvl *)
  | Public, _ -> Some b 
  | _, Public -> Some a 
  | SNode(a_set), SNode(b_set) -> 
    
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
let meet_of_integrity_lvls (pol : cst_access_policy) (a : integrity_lvl) (b : integrity_lvl) : integrity_lvl option = 
  match (a, b) with 
  (* if one integrity_lvl is Untrusted, the greatest lower bound is the other integrity_lvl *)
  | Untrusted, _ -> Some b
  | _, Untrusted -> Some a 
  | INode(a_set), INode(b_set) -> 
    
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



(* reads whether lvl_a is less than or equal to lvl_b *)
let leq_secrecy (secrecy_lattice : cst_access_policy) (lvl_a : secrecy_lvl) (lvl_b : secrecy_lvl) = 
  match lvl_a, lvl_b with 
  (* Public is smaller than every secrecy lvl *)
  | Public, _ -> true 
  | SNode(a_set), SNode(b_set) -> 
    let comparison, rel = secrecy_lattice in
    begin match rel with 
    | GreaterThanOrEqual -> 
      (* This is a sub-optimal way to compute, but for now we need it due to the way that secrecy_lattice is built *)
      let eq = ProcTySet.equal a_set b_set in 
      let a_set_geq_b_set = (List.assoc (a_set, b_set) comparison) in 
      (not a_set_geq_b_set) || eq
    | LessThanOrEqual -> (raise (LatticeException "cannot call leq_secrecy on an integrity lattice"))
    end 
  | _, _ -> false 


(* reads whether integrity lvl a is less than or equal to integrity lvl b *)
let leq_integrity (integrity_lattice : cst_access_policy) (lvl_a : integrity_lvl) (lvl_b : integrity_lvl) = 
  match lvl_a, lvl_b with 
  (* Every element is less than or equal to Untrusted *)
  | _, Untrusted -> true 


  | INode(a_set), INode(b_set) -> 
    let comparison, rel = integrity_lattice in 

    begin match rel with 
    | LessThanOrEqual -> 
      (List.assoc (a_set, b_set) comparison)
    | GreaterThanOrEqual -> 
      (raise (LatticeException "cannot call leq_integrity on a secrecy lattice"))
    end
  | _, _ -> false
