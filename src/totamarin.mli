val separator : string ref

type to_tamarin_error

exception Error of to_tamarin_error Location.located

val error : loc:Location.t -> to_tamarin_error -> 'error

val print_error : to_tamarin_error -> Format.formatter -> unit

type mindex = (int list * int) list

type functions = (string * int) list

type expr =
    FVar of expr
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
type rule_config = { is_persist : bool; priority : int; }

type fact =
    Fact of string * string * expr list
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

val mk_constant_fact : string -> fact

type fact' = string * expr list * rule_config

type action =
    ActionReturn of expr
  | ActionAssign of (int * bool) * expr
  | ActionSeq of action * action
  | ActionAddMeta of int
  | ActionIntro of expr list
  | ActionPopLoc of int
  | ActionPopMeta of int
  | ActionLetTop of expr list

type state = {
  state_namespace : string;
  state_index : (int list * int) list;
  state_vars : int * int * int;
}

val state_index_to_string_aux : state -> string

type transition = {
  transition_id : int;
  transition_namespace : string;
  transition_name : string;
  transition_from : state;
  transition_to : state;
  transition_pre : fact list;
  transition_post : fact list;
  transition_state_transition :
    (expr * expr list * expr list * expr list) *
    (expr * expr list * expr list * expr list);
  transition_label : fact list;
  transition_is_loop_back : bool;
}

val print_transition : transition -> bool -> string

type rule =
    Rule of string * string * fact' list * fact' list * fact' list
  | Comment of string

type model = {
  model_name : string;
  model_states : state list;
  model_transitions : transition list;
  model_init_rules : rule list;
  model_init_state : state;
  model_transition_id_max : int;
  model_type : string;
}

val add_transition : model -> transition -> model

type lemma =
    PlainLemma of string * string
  | ReachabilityLemma of string * string list * string list * string list *
                         fact list * fact list
  | CorrespondenceLemma of string * string list * (fact list * fact) *
                           (fact list * fact)

type tamarin = signature * model list * rule list * lemma list

val print_tamarin : tamarin -> bool -> bool -> string

val translate_sys :
  Context.system -> string list * string list -> tamarin
