module T = Typed
open Rabbit_proverif_pv_parse
open Pitptree

module Error = struct
  type error =
    | Unsupported of string
    | Invalid_input of string
    | Internal_error of string

  exception Error of error Location.located

  let _error ~loc err = Stdlib.raise (Error (Location.locate ~loc err))

  let _error_ex ex ~loc fmt = Printf.ksprintf (fun s -> _error ~loc (ex s)) fmt

  let unsupported ~loc fmt = _error_ex (fun s -> Unsupported s) ~loc fmt
  let invalid_input ~loc fmt = _error_ex (fun s -> Invalid_input s) ~loc fmt
  let internal ~loc fmt = _error_ex (fun s -> Internal_error s) ~loc fmt

  let print_error err ppf =
    match err with
    | Unsupported s -> Format.pp_print_string ppf s
    | Invalid_input s -> Format.pp_print_string ppf s
    | Internal_error s -> Format.pp_print_string ppf s
end

let with_dummy_ident_ext x = x, Parsing_helper.dummy_ext

let with_dummy_node_ext x = x, Parsing_helper.dummy_ext, []

let pv_ident (s : string) : ident = with_dummy_ident_ext s

let compile_ident (id : T.ident) : ident = pv_ident (Ident.to_string id)

let bitstring_ident             = pv_ident "bitstring"
let channel_ident               = pv_ident "channel"
let param_data_ident            = pv_ident "param_data"
let proc_t_ident                = pv_ident "proc_t"
let acc_data_t_ident            = pv_ident "acc_data_t"
let syscall_t_ident             = pv_ident "syscall_t"
let access_control_table_ident  = pv_ident "access_control_table"
let file_type_table_ident       = pv_ident "file_type_table"
let channel_table_ident         = pv_ident "channel_table"
let deleted_address_table_ident = pv_ident "deleted_address_table"
let attacker_channel_ident      = pv_ident "attacker"
let true_ident                  = pv_ident "true"
let false_ident                 = pv_ident "false"
let ptype_arg_ident             = pv_ident "ptype"
let none_syscall_ident          = pv_ident "none_syscall_s"
let precise_ident               = pv_ident "precise"
let term_e    (t : term)     : term_e     = with_dummy_node_ext t
let pterm_e   (t : pterm)    : pterm_e    = with_dummy_node_ext t
let gterm_e   (t : gterm)    : gterm_e    = with_dummy_node_ext t
let process_e (p : tprocess) : tprocess_e = with_dummy_node_ext p
let tquery_e  (q : tquery)   : tquery_e   = with_dummy_node_ext q

let add_comment c (a, b, comments) = (a, b, c :: comments)

let compile_name (name : T.name) : ident = pv_ident name

(* "Struct" for "Struct" *)
let structure_ctor_ident (name : T.name) : ident =
  compile_name name

(* "StructAddr" for "Struct" *)
let structure_addr_ident (name : T.name) : ident =
  pv_ident (name ^ "Addr")

(* "StructPar1" for "Struct" and 1 *)
let structure_arg_ident (name : T.name) (index : int) : ident =
  pv_ident (Printf.sprintf "%sPar%d" name index)

module Int : sig
  val to_term_e : int -> term_e
  val to_pterm_e : int -> pterm_e
  val to_gterm_e : int -> gterm_e
end = struct
  let zero_term_e () : term_e = term_e @@ PIdent (pv_ident "0")
  let zero_pterm_e () : pterm_e = pterm_e @@ PPIdent (pv_ident "0")
  let zero_gterm_e () : gterm_e = gterm_e @@ PGIdent (pv_ident "0")

  let rec unfold (t : term_e) (n : int) : term_e =
    match n with
    | 0 -> t
    | n ->
        term_e @@ PFunApp (pv_ident "+", [unfold t (n - 1)])

  let unfold_minus (t : term_e) (n : int) : term_e =
    match n with
    | 0 -> t
    | n ->
        term_e @@ PFunApp (pv_ident ("- " ^ string_of_int n), [t])

  let rec unfold_pterm (t : pterm_e) (n : int) : pterm_e =
    match n with
    | 0 -> t
    | n ->
        pterm_e @@ PPFunApp (pv_ident "+", [unfold_pterm t (n - 1)])

  let unfold_minus_pterm (t : pterm_e) (n : int) : pterm_e =
    match n with
    | 0 -> t
    | n ->
        pterm_e @@ PPFunApp (pv_ident ("- " ^ string_of_int n), [t])

  let rec unfold_gterm (t : gterm_e) (n : int) : gterm_e =
    match n with
    | 0 -> t
    | n ->
        gterm_e @@ PGFunApp (pv_ident "+", [unfold_gterm t (n - 1)], None)

  let unfold_minus_gterm (t : gterm_e) (n : int) : gterm_e =
    match n with
    | 0 -> t
    | n ->
        gterm_e @@ PGFunApp (pv_ident ("- " ^ string_of_int n), [t], None)

  let to_term_e (n : int) : term_e =
    if n >= 0 then
      unfold (zero_term_e ()) n
    else
      (* Negative integer -n is represented as `0 - n` *)
      unfold_minus (zero_term_e ()) (-n)

  let to_pterm_e (n : int) : pterm_e =
    if n >= 0 then
      unfold_pterm (zero_pterm_e ()) n
    else
      unfold_minus_pterm (zero_pterm_e ()) (-n)

  let to_gterm_e (n : int) : gterm_e =
    if n >= 0 then
      unfold_gterm (zero_gterm_e ()) n
    else
      unfold_minus_gterm (zero_gterm_e ()) (-n)
end
