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



type proc_ty = Ident.t
type syscall_desc = Typed.syscall_desc

module ProcSyscallPair = struct
  type t = proc_ty * syscall_desc
  
  let compare (proc1, syscall1) (proc2, syscall2) =
    let proc_cmp = Ident.compare proc1 proc2 in
    if proc_cmp = 0 then
      Typed.compare_syscall_desc syscall1 syscall2
    else
      proc_cmp
      
  let pp fmt (proc_ty, syscall_desc) =
    Format.fprintf fmt "(%a, %a)" 
      Ident.pp proc_ty
      Typed.pp_syscall_desc syscall_desc
      
  let equal (proc1, syscall1) (proc2, syscall2) =
    Ident.equal proc1 proc2 && Typed.equal_syscall_desc syscall1 syscall2
end

module ProcSyscallSet = Set.Make(ProcSyscallPair)
