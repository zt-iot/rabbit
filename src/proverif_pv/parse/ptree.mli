(* Terms *)

type ident = string * Parsing_helper.extent

type term = 
    PIdent of ident
  | PFunApp of ident * term list
  | PTuple of term list
  | PName of ident * term list

type format = 
    PFIdent of ident
  | PFFunApp of ident * format list
  | PFTuple of format list
  | PFName of ident * format list
  | PFAny of ident

(* Clauses *)

type fact = 
    PSimpleFact of ident * term list
  | PSNeq of term * term

type fact_e = fact * Parsing_helper.extent

type format_fact = ident * format list

type clause = 
    Clause of fact_e list * fact_e 
  | Equiv of fact_e list * fact_e * bool

type pval = 
    S of ident
  | I of int

(* Declarations - untyped front-end *)

type decl = 
    FunDecl of ident * int
  | DataFunDecl of ident * int
  | Equation of (term * term) list
  | Query of fact_e
  | NoUnif of format_fact * Types.nounif_value
  | Not of fact_e
  | Elimtrue of fact_e
  | PredDecl of ident * int * ident list
  | Param of ident * pval
  | Reduc of clause list

(* Declarations - typed front-end *)

type envdecl = (ident(*variable*) * ident(*type*)) list

type tdecl = 
    TTypeDecl of ident (* type declaration *)
  | TNameDecl of ident * ident(*type*)
  | TFunDecl of ident * ident list(*argument types*) * ident(*result type*) * ident list(*options*)
  | TConstDecl of ident * ident(*type*) * ident list(*options*)
  | TEquation of (envdecl * term * term) list * ident list(*options*)
  | TQuery of envdecl * fact_e
  | TNoUnif of envdecl * format_fact * Types.nounif_value
  | TNot of envdecl * fact_e
  | TElimtrue of envdecl * fact_e
  | TPredDecl of ident * ident list(*argument types*) * ident list(*options*)
  | TSet of ident * pval
  | TReduc of (envdecl * clause) list


