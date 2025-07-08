
open Sets 
open Maps


type syscall_effect = 
  | Read 
  | Provide 
  | ReadProvide


type syscall_effect_map = (syscall_effect) string_map 

val syscall_effect_map : syscall_effect_map

type access_map = (proc_ty_set) security_type_map

val create_access_maps : Typed.decl list -> access_map * access_map


val convert : Typed.decl list -> Cst_syntax.decl list