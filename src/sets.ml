module StringSet = Set.Make(String)
module ProcTySet = Set.Make(String)
module SecurityTypeSet = Set.Make(String)

module ProcTySetSet = Set.Make(ProcTySet)

type proc_ty_set = ProcTySet.t 


let pp_proc_ty_set fmt set =
  Format.fprintf fmt "{ ";
  ProcTySet.iter (fun s -> Format.fprintf fmt "%s; " s) set;
  Format.fprintf fmt "}"


let equal_proc_ty_set = ProcTySet.equal