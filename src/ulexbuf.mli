(** The state of the parser: a stream, a beginning- and an end-position. *)
type t = private {
  stream : Sedlexing.lexbuf ;
  mutable pos_start : Lexing.position ;
  mutable pos_end : Lexing.position ;
  mutable line_limit : int option ;
  mutable end_of_input : bool ;

  mutable used_idents : string list;
  mutable used_strings : string list;
}

type error =
  | SysError of string
  | Unexpected of string
  | MalformedUTF8
  | BadNumeral of string
  | UnclosedComment

include Sig.ERROR with type error := error

(** Update the start and end positions from the stream. *)
val update_pos : t -> unit
(** Register [n] new lines in the lexbuf's position. *)
val new_line : ?n:int -> t -> unit
(** The last matched lexeme as a string  *)
val lexeme : t -> string
(** Create a lex-buffer from a channel. Set filename to [fn] (default ["?"]) *)
val from_channel : ?fn:string -> in_channel -> t
(** Create a lex-buffer from a string. Set filename to [fn] (default ["?"]) *)
val from_string : ?fn:string -> string -> t

val reached_end_of_input : t -> unit
val set_line_limit : int option -> t -> unit

val record_ident : string -> t -> unit

val record_string : string -> t -> unit
