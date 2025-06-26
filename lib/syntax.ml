

type variable_desc =
  | Top of int  (* variables declared in memory instantiation of a process *)
  (* Loc is used for a lot of things: 
    let statements in process, 
    "x := ..." stmts, in `equation a(x) = b(y)`, 
    the parameters `x, y` in `syscall a(x, y) { ... }`/ `passive attack ...
    the parameters `x, y` in member functions `function (x, y) {...}` of a process template
    and variables within a `lemma`
    *)
  | Loc of int
  | Meta of int



type operator = string 


type expr = 
  | Variable of string * variable_desc
  | Apply of operator * expr list
  | Tuple of expr list

type fact = 
  | Fact of Name.ident * expr list
  | GlobalFact of Name.ident * expr list
  | ChannelFact of expr * Name.ident * expr list
  | EqFact of expr * expr
  | NeqFact of expr * expr
  | FileFact of expr * expr


(* meta vars, local vars, top-level variables *)
(* type local_typing_context = Name.ident list * Name.ident list * Name.ident list *)

type 'cmd case = fact list * 'cmd

type cmd =
  | Skip
  | Sequence of cmd * cmd
  | Put of fact list
  | Let of Name.ident * expr * cmd
  | Assign of Name.ident option * expr
  | Case of cmd case list
  | While of cmd case list * cmd case list
  | Event of fact list
  | Return of expr

  | New of Name.ident * (Name.ident * expr list) option * cmd 
  | Get of Name.ident list * expr * Name.ident * cmd
  | Del of expr * Name.ident
  


(* system instantiation *)
type lemma = 
  | PlainLemma of { name : Name.ident; desc : string }
  | ReachabilityLemma of { name : Name.ident; fresh_variables : Name.ident list; facts : fact list }
  | CorrespondenceLemma of { name : Name.ident; fresh_variables : Name.ident list; premise : fact; conclusion : fact }

