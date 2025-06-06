val separator : string ref
val fresh_ident : string ref
val fresh_string : string ref
val fresh_param : string ref

val int_to_list : int -> int list
val contains : string -> string -> bool

type mindex = (int list * int) list
type functions = (string * int) list

type expr =
  | FVar of expr
  | Var of string
  | MetaVar of int
  | LocVar of int
  | TopVar of int
  | MetaNewVar of int
  | Apply of string * expr list
  | String of string
  | Integer of int
  | List of expr list
  | One
  | Int of string
  | AddOne of expr
  | Unit
  | Param

val print_expr : expr -> string

type equations = (expr * expr) list
type signature = functions * equations

val empty_signature : signature

type rule_config =
  { is_persist : bool
  ; priority : int
  }

val config_linear : rule_config
val config_persist : rule_config

type fact =
  | Fact of string * string * expr list
  | ConstantFact of expr * expr
  | GlobalFact of string * expr list
  | ChannelFact of string * expr * expr list
  | PathFact of string * string * expr * expr list
  | ProcessFact of string * expr * expr list
  | ResFact of int * expr list
  | AccessFact of string * expr * expr * string
  | AttackFact of string * expr
  | FileFact of string * expr * expr
  | InitFact of expr list
  | LoopFact of string * mindex * int
  | TransitionFact of string * string * expr * expr
  | InjectiveFact of string * string * expr * expr
  | FreshFact of expr
  | AccessGenFact of string * expr

type fact' =
  { name : string
  ; args : expr list
  ; config : rule_config
  }

val print_fact' : fact -> fact'

val mk_constant_fact : string -> fact

type action =
  | ActionReturn of expr
  | ActionAssign of Syntax.variable_desc * expr
  | ActionSeq of action * action
  | ActionAddMeta of int
  | ActionIntro of expr list
  | ActionPopLoc of int
  | ActionPopMeta of int
  | ActionLetTop of expr list

type state =
  { state_namespace : string
  ; state_index : (int list * int) list
  ; state_vars : int * int * int
  }

type transition =
  { transition_id : int
  ; transition_namespace : string
  ; transition_name : string
  ; transition_from : state
  ; transition_to : state
  ; transition_pre : fact list
  ; transition_post : fact list
  ; transition_state_transition :
      (expr * expr list * expr list * expr list)
      * (expr * expr list * expr list * expr list)
  ; transition_label : fact list
  ; transition_is_loop_back : bool
  }

val mk_state_transition_from_action
  :  action
  -> int * int * int
  -> (expr * expr list * expr list * expr list)
     * (expr * expr list * expr list * expr list)

val state_index_to_string_aux : state -> string

val mk_state : ?param:string -> state -> expr * expr list * expr list * expr list -> fact'

type rule =
  | Rule of string * string * fact' list * fact' list * fact' list
  | Comment of string

type model =
  { model_name : string
  ; model_states : state list
  ; model_transitions : transition list
  ; model_init_rules : rule list
  ; model_init_state : state
  ; model_transition_id_max : int
  ; model_type : string
  }

val mk_state_transition
  :  ?param:string
  -> state
  -> expr * expr list * expr list * expr list
  -> bool
  -> bool
  -> fact'

val initial_model : string -> string -> model * state

val initial_state : string -> state

val add_transition : model -> transition -> model

val add_state : model -> state -> model

type lemma =
  | PlainLemma of string * string
  | ReachabilityLemma of
      string * string list * string list * string list * fact list * fact list
  | CorrespondenceLemma of string * string list * (fact list * fact) * (fact list * fact)

type tamarin = {
  signature : signature;
  models : model list;
  rules : rule list;
  lemmas : lemma list
}

val empty_tamarin : tamarin

val add_fun : tamarin -> string * int -> tamarin

val add_const : tamarin -> string -> tamarin

val add_eqn : tamarin -> expr * expr -> tamarin

val add_model : tamarin -> model -> tamarin

val add_rule
  :  tamarin
  -> string * string * fact list * fact list * fact list
  -> tamarin

val add_rule'
  :  tamarin
  -> string * string * fact' list * fact' list * fact' list
  -> tamarin

val add_comment : tamarin -> string -> tamarin

val add_lemma : tamarin -> lemma -> tamarin

val print_transition : transition -> bool -> string

val print_tamarin : tamarin -> bool -> bool -> string
