type indexed_var = Name.ident * int * int
type operator = string 
let index_var s (i, j) = (s, i, j)

type expr = expr' Location.located
and expr' =
  | Const of Name.ident
  | ExtConst of Name.ident
  | Variable of indexed_var
  | Boolean of bool
  | String of string
  | Integer of int
  | Float of string (* store the string so we can correctly round later *)
  | Apply of operator * expr list
  | Tuple of expr list
  | Channel of string 

type instructions = 
  | IRead | IWrite | IInvoke | IRecv | ISend | IOpen | IClose | ICloseConn | IConnect | IAccept


type atomic_stmt = atomic_stmt' Location.located
and atomic_stmt' = 
  | Skip
  | Let of indexed_var * expr
  | Call of indexed_var * Name.ident * expr list
  | Instruction of indexed_var * instructions * expr list
  | If of expr * stmt list * stmt list
  | For of indexed_var * int * int * stmt list

and event = event' Location.located
and event' = 
  | Event of Name.ident * ((indexed_var * bool) list)

and stmt = stmt' Location.located
and stmt' = 
  | OpStmt of atomic_stmt
  | EventStmt of atomic_stmt * event list


type proc = proc' Location.located
and proc' =
  | Proc of Name.ident * (Name.ident list) * Name.ident

type fpath = fpath' Location.located
and fpath' = 
  | Fpath of (Name.ident * expr * Name.ident)

type prop = prop' Location.located
and prop' =
  | True

type lemma = lemma' Location.located
and lemma' =
  | Lemma of Name.ident * prop 

type sys = sys' Location.located
and sys' = 
  | Sys of proc list * lemma list


let pprint_iv (v, i, j) ppf =
   Format.fprintf ppf "%s[%d,$d]" v i j
  
let string_of_isn i =   
  match i with 
  | IRead -> "read" | IWrite -> "write" | IInvoke -> "invoke" | IRecv -> "recv" | ISend -> "send" | IOpen -> "open" | IClose -> "close" | ICloseConn -> "close_conn" 
  | IConnect -> "connect" | IAccept -> "accept"

let pprint_ins i ppf = 
   Format.fprintf ppf i

let print_iv (v, i, j) =
    "%s[%d,$d]" v i j

let pprint_ins i = string_of_isn i 
(* 
let pprint_expr {Location.data=c; Location.loc=loc} ppf = 
    let print_expr' = function
    | Const s -> Format.fprintf ppf "Const %s" s 
    | ExtConst s -> Format.fprintf ppf "ExtConst %s" s
    | Variable iv -> pprint_iv iv ppf 
    | Boolean b -> Format.fprintf ppf "Bool %b" b
    | String s -> Format.fprintf ppf "String %s" s
    | Integer k -> Format.fprintf ppf "Int %d" k
    | Float s -> Format.fprintf ppf "Float %s" k
    | Apply (o, el) -> Format.fprintf ppf "%s(";  k  o^(List.fold_left (fun a b -> a ^" "^ print_expr b) "" el)
    | Tuple el -> (List.fold_left (fun a b -> a ^" "^ print_expr b) "" el)
    | Channel s -> "ch "^s
  in let c = print_expr' c in "("^c^")"

 *)

let rec print_expr {Location.data=c; Location.loc=loc} = 
   let print_expr' = function
    | Const s -> "Const " ^s 
    | ExtConst s -> "ExtConst " ^s
    | Variable iv -> print_iv iv
    | Boolean b -> string_of_bool b 
    | String s -> s
    | Integer k -> string_of_int k
    | Float s -> s
    | Apply (o, el) -> o^(List.fold_left (fun a b -> a ^" "^ print_expr b) "" el)
    | Tuple el -> (List.fold_left (fun a b -> a ^" "^ print_expr b) "" el)
    | Channel s -> "ch "^s
  in let c = print_expr' c in "("^c^")"

let rec print_stmt {Location.data=c; Location.loc=loc} = 
  let print_stmt' = function
  | OpStmt a -> print_atomic_stmt a
  | EventStmt (a, el) -> print_atomic_stmt a ^ " @ "^(List.fold_left (fun a b -> a ^" "^ print_event b) "" el)
in let c = print_stmt' c in  "("^c^")"

and print_atomic_stmt {Location.data=c; Location.loc=loc} = 
  let print_atomic_stmt' = function
    | Skip -> "Skip"
    | Let (iv, e) -> (print_iv iv) ^ " := " ^ (print_expr e)
    | Call (iv, f, args) -> (print_iv iv) ^ " := " ^ f ^ (List.fold_left (fun a b -> a ^" "^ print_expr b) "" args)
    | Instruction (iv, ins, args) -> (print_iv iv) ^ " := " ^ (print_instruction ins) ^ (List.fold_left (fun a b -> a ^" "^ print_expr b) "" args)
    | If (e, c1, c2) -> "if " ^ (print_expr e) ^ " then " ^ (List.fold_left (fun a b -> a ^";"^ print_stmt b) "" c1) ^ " then " ^ (List.fold_left (fun a b -> a ^";"^ print_stmt b) "" c2)
    | For (iv, i, j, c) -> "for " ^ (print_iv iv) ^ " in ["^(string_of_int i) ^", "^(string_of_int j)^"] do "^(List.fold_left (fun a b -> a ^";"^ print_stmt b) "" c)
in let c = print_atomic_stmt' c in "("^c^")"

and print_event {Location.data=c; Location.loc=loc} = 
   let print_event' = function
   | Event (eid, ivl) -> eid^"("^(List.fold_left (fun a (iv, b) -> a ^" "^ (print_iv iv) ^ ":"^(string_of_bool b)) "" ivl)^")"
 in let c = print_event' c in "("^c^")"











