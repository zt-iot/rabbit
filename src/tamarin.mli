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

type signature =
  { functions : functions
  ; equations : equations
  }

val empty_signature : signature

type rule_config =
  { is_persist : bool
  ; priority : int
  }

val config_linear : rule_config
val config_persist : rule_config

type state_desc =
  { ret : expr
  ; metas : expr list
  ; locs : expr list
  ; tops : expr list
  }

val empty_state_desc : state_desc
val map_state_desc : (expr -> expr) -> state_desc -> state_desc

type var_nums =
  { meta : int
  ; loc : int
  ; top : int
  }

type state =
  { state_namespace : string
  ; state_index : mindex
  ; state_vars : var_nums
  }

type fact =
  | Fact of string * string * expr list
  | ConstantFact of expr * expr
  | GlobalFact of string * expr list
  | ChannelFact of string * expr * expr list
  | PathFact of string * string * expr * expr list
  | ProcessFact of string * expr * expr list
  | EqFact of expr * expr
  | NeqFact of expr * expr
  | AccessFact of string * expr * expr * string
  | AttackFact of string * expr
  | FileFact of string * expr * expr
  | InitFact of expr list
  | LoopFact of string * mindex * int
  | TransitionFact of string * string * expr * expr
  | InjectiveFact of string * string * expr * expr
  | FreshFact of expr
  | FreshFact' of expr
  (** It was once [ResFact(2, [e])]. Compilation is slightly different from [FreshFact] *)
  | AccessGenFact of string * expr
  | StateFact of
      { param : string option
      ; state : state
      ; state_desc : state_desc
      ; transition : expr option
      }

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

type transition =
  { transition_id : int
  ; transition_namespace : string
  ; transition_name : string
  ; transition_from : state
  ; transition_to : state
  ; transition_pre : fact list
  ; transition_post : fact list
  ; transition_state_transition : state_desc * state_desc
  ; transition_label : fact list
  ; transition_is_loop_back : bool
  }

val mk_state_transition_from_action : action -> var_nums -> state_desc * state_desc
val state_index_to_string_aux : state -> string

type 'fact rule_ =
  { name : string
  ; role : string
  ; pre : 'fact list
  ; label : 'fact list
  ; post : 'fact list
  }

type rule =
  | Rule of fact rule_
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

val mk_state_fact : ?param:string -> state -> state_desc -> expr option -> fact
val mk_transition_expr : [ `Initial | `Loop | `None ] -> expr
val initial_model : namespace:string -> typ:string -> model * state
val add_transition : model -> transition -> model
val add_state : model -> state -> model

type lemma =
  | PlainLemma of string * string
  | ReachabilityLemma of string * fact list * fact list
  | CorrespondenceLemma of string * string list * (fact list * fact) * (fact list * fact)

type tamarin =
  { signature : signature
  ; models : model list
  ; rules : rule list
  ; lemmas : lemma list
  }

(** Empty Tamarin code *)
val empty_tamarin : tamarin

(** Add external function with arity *)
val add_fun : tamarin -> string * int -> tamarin

(** Add external constant as a nullary funciton *)
val add_const : tamarin -> string -> tamarin

(** Add an equation *)
val add_eqn : tamarin -> expr * expr -> tamarin

(** Add a model *)
val add_model : tamarin -> model -> tamarin

(** Add a rule of [fact] *)
val add_rule : tamarin -> fact rule_ -> tamarin

(** Add a comment *)
val add_comment : tamarin -> string -> tamarin

(** Add a lemma *)
val add_lemma : tamarin -> lemma -> tamarin

val print_transition : transition -> dev:bool -> string
val print_tamarin : tamarin -> dev:bool -> print_transition_label:bool -> string
