type variable_desc =
  
  
  (* Loc is used for a lot of things: 
    let statements in process, 
    "x := ..." stmts, in `equation a(x) = b(y)`, 
    the parameters `x, y` in `syscall a(x, y) { ... }`/ `passive attack ...
    the parameters `x, y` in member functions `function (x, y) {...}` of a process template
    and variables within a `lemma`
    *)
  | Top of int  (* variables declared in memory instantiation of a process *)
  | Loc of int
  | Meta of int


type indexed_var = Name.ident * int * int * int
type operator = string 


type expr = expr' Location.located
and expr' =
  | Const of Name.ident * expr option
  | ExtConst of Name.ident (* we require this as opposed to just Apply, due to some 0-argument equational theory functions such as function true:0 *)
  | Variable of string * variable_desc
  | Boolean of bool
  | String of string
  | Integer of int
  | Float of string (* store the string so we can correctly round later *)
  | Apply of operator * expr list
  | Tuple of expr list
  | Channel of Name.ident 

type fact = fact' Location.located
and fact' = 
  | Fact of Name.ident * expr list
  | GlobalFact of Name.ident * expr list
  | ChannelFact of expr * Name.ident * expr list
  | ProcessFact of Name.ident * Name.ident * expr list
  | EqFact of expr * expr
  | NeqFact of expr * expr
  | FileFact of expr * expr




(* meta vars, local vars, top-level variables *)
(* type local_typing_context = Name.ident list * Name.ident list * Name.ident list *)

type cmd = cmd' Location.located
and cmd' = 
  | Skip
  | Sequence of cmd * cmd
  | Put of fact list
  | Let of Name.ident * expr * cmd
  | Assign of (Name.ident * (int * bool)) * expr (* (k, true) : k'th in top-level (k, false): k'th in local *)
  | FCall of (Name.ident * (int * bool)) option * Name.ident * expr list
  | SCall of (Name.ident * (int * bool)) option * Name.ident * expr list
  | Case of (string list * fact list * cmd) list
  | While of (string list * fact list * cmd) list * (string list * fact list * cmd) list
  | Event of fact list
  | Return of expr

  | New of Name.ident * Name.ident * expr list * cmd 
  | Get of Name.ident list * expr * Name.ident * cmd
  | Del of expr * Name.ident

(* last one is type` *)
type chan_arg = 
  | ChanArgPlain of string * string 
  | ChanArgParam of string * string 
  | ChanArgParamInst of string * expr * string


type proc = proc' Location.located
and proc' =
  | Proc of Name.ident * (Name.ident list) * Name.ident

type fpath = fpath' Location.located
and fpath' = 
  | Fpath of (Name.ident * expr * Name.ident)

type lemma = lemma' Location.located
and lemma' = 
  | PlainLemma of { name : Name.ident; desc : string }
  | ReachabilityLemma of { name : Name.ident; fresh_variables : Name.ident list; facts : fact list }
  | CorrespondenceLemma of { name : Name.ident; fresh_variables : Name.ident list; premise : fact; conclusion : fact }

