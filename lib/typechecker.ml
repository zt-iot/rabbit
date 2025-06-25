
open Sets
open Maps


(* a plain_ty is a Rabbit type without security information *)
type plain_ty = 
  | Unit 
  | PlainTyp of Name.ident * rabbit_ty list
  | ChannelTyp of rabbit_ty list
  | ProdTyp of rabbit_ty * rabbit_ty
[@@deriving show, eq]

and secrecy_lvl = 
  | Public (* denote all processes *)
  | SNode of proc_set (* denote a subset of processes which are allowed to read a specific type *)
[@@deriving show, eq]

and integrity_lvl = 
  | Untrusted (* denotes all processes *) 
  | INode of proc_set (* denotes a subset of processes which are allowed to provide a certain type *)
[@@deriving show, eq]

and security_lvl = secrecy_lvl * integrity_lvl [@@deriving show, eq]


and rabbit_ty = 
  | RabbitTyp of plain_ty * security_lvl (* every rabbit_ty will have an explicit security level *)
[@@deriving show, eq]


type function_ty = 
  | FunTyp of rabbit_ty list (* FunTyp of 0-length list is ill-typed *)


(* the type which is used as the value type of our typing environment *)
type env_value_ty = 
  | ValueRabbitTyp of rabbit_ty
  | ValueFunTyp of function_ty (* the reason we introduce a function_ty is because function types do not have a security level *)



let rec typeof_expr e env = match e with 
  | Syntax.Variable(x, _) -> 
    begin 
      match StringMap.find x env with
      | ValueRabbitTyp(rtyp) -> rtyp
      | ValueFunTyp(_) -> failwith "A variable cannot be of function type"
    end
  | Syntax.Apply(sym, es) -> begin
      match StringMap.find sym env with 
      | ValueFunTyp(FunTyp(ts)) -> begin
        failwith "TODO"
        end
      | ValueRabbitTyp(_) -> failwith (Printf.sprintf "%s must be a function type" sym)
      end
  | Syntax.Tuple(es) -> failwith "TODO"  
  | _ -> failwith "TODO"

let rec typecheck_fact env () = failwith "TODO"

(* let rec typeof_cmd env (cmd : Syntax.cmd) = match cmd with 
  |  *)



