
open Sets
open Maps


(* a plain_ty is a Rabbit type without security information *)
type plain_ty = 
  | Unit 
  | PlainTyp of Name.ident * rabbit_ty list
  | ChannelTyp of rabbit_ty list
  | ProdTyp of rabbit_ty * rabbit_ty
[@@deriving show]

and secrecy_lvl = 
  | Public (* denote all processes *)
  | SNode of proc_set (* denote a subset of processes which are allowed to read a specific type *)

and integrity_lvl = 
  | Untrusted (* denotes all processes *) 
  | INode of proc_set (* denotes a subset of processes which are allowed to provide a certain type *)


and security_lvl = secrecy_lvl * integrity_lvl [@@deriving show]


and rabbit_ty = 
  | RabbitTyp of plain_ty * security_lvl (* every rabbit_ty will have an explicit security level *)
[@@deriving show]

let pp_secrecy_lvl fmt v = match v with
  | Public -> Format.fprintf fmt "Public"
  | SNode p -> Format.fprintf fmt "SNode(%a)" pp_proc_set p

let pp_integrity_lvl fmt v = match v with
  | Untrusted -> Format.fprintf fmt "Untrusted"
  | INode p -> Format.fprintf fmt "INode(%a)" pp_proc_set p

let equal_secrecy_lvl s1 s2 =
  match s1, s2 with
  | Public, Public -> true
  | SNode p1, SNode p2 -> ProcSet.equal p1 p2
  | _, _ -> false


let equal_integrity_lvl i1 i2 =
  match i1, i2 with
  | Untrusted, Untrusted -> true
  | INode p1, INode p2 -> ProcSet.equal p1 p2
  | _, _ -> false


let equal_security_lvl (s1, i1) (s2, i2) =
  equal_secrecy_lvl s1 s2 && equal_integrity_lvl i1 i2

let rec equal_plain_ty t1 t2 =
  match t1, t2 with
  | Unit, Unit -> true
  | PlainTyp (id1, args1), PlainTyp (id2, args2) ->
      id1 = id2 && List.for_all2 equal_rabbit_ty args1 args2
  | ChannelTyp lst1, ChannelTyp lst2 ->
      List.for_all2 equal_rabbit_ty lst1 lst2
  | ProdTyp (a1, b1), ProdTyp (a2, b2) ->
      equal_rabbit_ty a1 a2 && equal_rabbit_ty b1 b2
  | _, _ -> false

and equal_rabbit_ty r1 r2 =
  match r1, r2 with
  | RabbitTyp (t1, s1), RabbitTyp (t2, s2) ->
      equal_plain_ty t1 t2 && equal_security_lvl s1 s2





let rec typeof_expr e env = match e with 
  | Syntax.Variable(x, _) -> StringMap.find x env
  | _ -> failwith "TODO"  




let rec typecheck_fact env () = failwith "TODO"

let rec typeof_cmd env (cmd : Syntax.cmd) = failwith "TODO"



