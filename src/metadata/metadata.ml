open Sexplib.Std

type loc =
  { filename : string option
  ; begin_line : int option
  }
[@@deriving sexp]

type fact_type =
  | Channel
  | Global
  | Eq
  | Neq
  | File
  | Fresh
  | ConstFresh
[@@deriving sexp]

type fact_info =
  { name : string
  ; loc : loc option
  ; ty : fact_type option
  ; fresh : string option
  ; paramvars : string list
  }
[@@deriving sexp]

type rule_info =
  { name : string
  ; pre : fact_info list
  ; label : fact_info list
  ; post : fact_info list
  ; attack : bool
  }
[@@deriving sexp]

type t = rule_info list [@@deriving sexp]
