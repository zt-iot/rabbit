(** Tamarin translation module for Rabbit
    This module provides functions to translate Rabbit models into Tamarin format.
    It defines the intermediate representation used during translation and provides
    functions to convert Rabbit models into Tamarin models. *)

(** Global separator string used in Tamarin output *)
val separator : string ref

(** Type representing multi-indexes in Tamarin *)
type mindex = (int list * int) list

(** Type representing function signatures in Tamarin *)
type functions = (string * int) list

(** Type representing expressions in Tamarin *)
type expr =
  | FVar of expr (** Function variable *)
  | Var of string (** Regular variable *)
  | MetaVar of int (** Meta variable *)
  | LocVar of int (** Local variable *)
  | TopVar of int (** Top-level variable *)
  | MetaNewVar of int (** New meta variable *)
  | Apply of string * expr list (** Function application *)
  | String of string (** String literal *)
  | Integer of int (** Integer literal *)
  | List of expr list (** List expression *)
  | One (** Unit value *)
  | Int of string (** Integer constant *)
  | AddOne of expr (** Increment expression *)
  | Unit (** Unit type *)
  | Param (** Parameter *)

(** Convert an expression to its string representation *)
val print_expr : expr -> string

(** Type representing equations in Tamarin *)
type equations = (expr * expr) list

(** Type representing function signatures and equations *)
type signature = functions * equations

(** Type representing rule configuration options *)
type rule_config = {
  is_persist : bool; (** Whether the rule is persistent *)
  priority : int; (** Priority of the rule *)
}

(** Type representing facts in Tamarin *)
type fact =
  | Fact of string * string * expr list (** General fact *)
  | ConstantFact of expr * expr (** Constant fact *)
  | GlobalFact of string * expr list (** Global fact *)
  | ChannelFact of string * expr * expr list (** Channel fact *)
  | PathFact of string * string * expr * expr list (** Path fact *)
  | ProcessFact of string * expr * expr list (** Process fact *)
  | ResFact of int * expr list (** Restriction fact *)
  | AccessFact of string * expr * expr * string (** Access control fact *)
  | AttackFact of string * expr (** Attack fact *)
  | FileFact of string * expr * expr (** File system fact *)
  | InitFact of expr list (** Initialization fact *)
  | LoopFact of string * mindex * int (** Loop fact *)
  | TransitionFact of string * string * expr * expr (** Transition fact *)
  | InjectiveFact of string * string * expr * expr (** Injective fact *)
  | FreshFact of expr (** Freshness fact *)
  | AccessGenFact of string * expr (** General access fact *)

(** Create a constant fact from a string *)
val mk_constant_fact : string -> fact

(** Type representing facts with configuration *)
type fact' = string * expr list * rule_config

(** Type representing actions in Tamarin *)
type action =
  | ActionReturn of expr (** Return action *)
  | ActionAssign of (int * bool) * expr (** Assignment action *)
  | ActionSeq of action * action (** Sequential actions *)
  | ActionAddMeta of int (** Add meta action *)
  | ActionIntro of expr list (** Introduction action *)
  | ActionPopLoc of int (** Pop local variable *)
  | ActionPopMeta of int (** Pop meta variable *)
  | ActionLetTop of expr list (** Let top action *)

(** Type representing states in Tamarin *)
type state = {
  state_namespace : string; (** State namespace *)
  state_index : (int list * int) list; (** State index *)
  state_vars : int * int * int; (** State variables *)
}

(** Convert state index to string representation *)
val state_index_to_string_aux : state -> string

(** Type representing transitions in Tamarin *)
type transition = {
  transition_id : int; (** Transition identifier *)
  transition_namespace : string; (** Transition namespace *)
  transition_name : string; (** Transition name *)
  transition_from : state; (** Source state *)
  transition_to : state; (** Target state *)
  transition_pre : fact list; (** Pre-conditions *)
  transition_post : fact list; (** Post-conditions *)
  transition_state_transition :
    (expr * expr list * expr list * expr list) *
    (expr * expr list * expr list * expr list); (** State transition details *)
  transition_label : fact list; (** Transition labels *)
  transition_is_loop_back : bool; (** Whether this is a loop-back transition *)
}

(** Convert transition to string representation *)
val print_transition : transition -> bool -> string

(** Type representing rules in Tamarin *)
type rule =
  | Rule of string * string * fact' list * fact' list * fact' list (** Rule with facts *)
  | Comment of string (** Comment *)

(** Type representing Tamarin models *)
type model = {
  model_name : string; (** Model name *)
  model_states : state list; (** List of states *)
  model_transitions : transition list; (** List of transitions *)
  model_init_rules : rule list; (** Initial rules *)
  model_init_state : state; (** Initial state *)
  model_transition_id_max : int; (** Maximum transition ID *)
  model_type : string; (** Model type *)
}

(** Add a transition to a model *)
val add_transition : model -> transition -> model

(** Type representing lemmas in Tamarin *)
type lemma =
  | PlainLemma of string * string (** Simple lemma *)
  | ReachabilityLemma of string * string list * string list * string list *
                           fact list * fact list (** Reachability lemma *)
  | CorrespondenceLemma of string * string list * (fact list * fact) *
                           (fact list * fact) (** Correspondence lemma *)

(** Type representing complete Tamarin model *)
type tamarin = signature * model list * rule list * lemma list

(** Convert Tamarin model to string representation *)
val print_tamarin : tamarin -> bool -> bool -> string

(** Translate Rabbit system to Tamarin format *)
val translate_sys :
  Context.system -> string list * string list -> tamarin
