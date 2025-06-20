module ProcSet = Set.Make(String)

type proc_set = ProcSet.t


let pp_proc_set fmt set =
  Format.fprintf fmt "{ ";
  ProcSet.iter (fun s -> Format.fprintf fmt "%s; " s) set;
  Format.fprintf fmt "}"