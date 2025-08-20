module StringSet = Set.Make(String)


module ProcTySet = Set.Make(String)

type proc_ty_set = ProcTySet.t


let equal_proc_ty_set = ProcTySet.equal

let pp_proc_ty_set fmt set =
  Format.fprintf fmt "{ ";
  ProcTySet.iter (fun s -> Format.fprintf fmt "%s; " s) set;
  Format.fprintf fmt "}"

let show_proc_ty_set x =
  Format.asprintf "%a" pp_proc_ty_set x


let compare : proc_ty_set -> proc_ty_set -> int = ProcTySet.compare


module SecurityTypeSet = Set.Make(Ident.IdentOrd)
module ProcTySetSet = Set.Make(ProcTySet)


type proc_ty = Ident.t
type sec_ty = Ident.t

type syscall_desc = Typed.syscall_desc



module ProcSyscallPair = struct
  type t = proc_ty * syscall_desc
  
  let compare (proc1, syscall1) (proc2, syscall2) =
    let proc_cmp = Ident.compare proc1 proc2 in
    if proc_cmp = 0 then
      Typed.compare_syscall_desc syscall1 syscall2
    else
      proc_cmp
      
end

module SecSyscallPair = struct 
  type t = sec_ty * syscall_desc

  let compare (sec1, syscall1) (sec2, syscall2) =
    let proc_cmp = Ident.compare sec1 sec2 in
    if proc_cmp = 0 then
      Typed.compare_syscall_desc syscall1 syscall2
    else
      proc_cmp
end



module ProcTySetPair = struct
  type t = proc_ty_set * proc_ty_set 

  let compare (a_set1, a_set2) (b_set1, b_set2) = 
    let c = ProcTySet.compare a_set1 b_set1 in
    if c <> 0 then c else ProcTySet.compare a_set2 b_set2
end



module ProcSyscallSet = Set.Make(ProcSyscallPair)


module SyscallDesc = struct
  type t = syscall_desc

  let compare syscall1 syscall2 = 
    Typed.compare_syscall_desc syscall1 syscall2 
end

module SyscallDescSet = Set.Make(SyscallDesc)

module SecSyscallSet = Set.Make(SecSyscallPair)


let proc_syscall_set_to_syscall_set (proc_syscall_set : ProcSyscallSet.t) : SyscallDescSet.t = 
  ProcSyscallSet.fold (fun (_, syscall_desc) acc_set -> 
      SyscallDescSet.add syscall_desc acc_set
    ) proc_syscall_set SyscallDescSet.empty


