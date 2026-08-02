open Lexing

let internal_error mess =
  print_string ("Internal error: " ^ mess ^ "\nPlease report bug to proverif-dev@inria.fr, including input file and output\n");
  exit 3

(* extent, for error messages *)

type extent = Lexing.position * Lexing.position

let dummy_ext = (Lexing.dummy_pos, Lexing.dummy_pos)

let merge_ext (p1,_) (_,p2) = (p1,p2)

let extent lexbuf =
  (Lexing.lexeme_start_p lexbuf,
   Lexing.lexeme_end_p lexbuf)

let set_start lexbuf (loc_start, _) =
  if loc_start != Lexing.dummy_pos then
    begin
      lexbuf.lex_abs_pos <- loc_start.pos_cnum;
      lexbuf.lex_start_p <- loc_start;
      lexbuf.lex_curr_p <- loc_start
    end
      
let parse_extent () =
  (Parsing.symbol_start_pos(),
   Parsing.symbol_end_pos())

exception InputError of string * extent

(* Add a point at the end of mess if neccessary *)
let add_point_if_necessary mess =
  if (String.length mess > 0) &&
    (let end_char = String.get mess (String.length mess - 1) in
    end_char != '.' && end_char != '?' && end_char != '!')
  then
    "."
else
    ""

(* Raise InputError *)
let input_error mess extent =
  raise (InputError (mess, extent))

let get_extent v (loc_start, loc_end) =
  if loc_start.pos_cnum = -1 then
    None
  else
    Some (
    let ch_start = loc_start.pos_cnum - loc_start.pos_bol + 1 in
    let ch_end = loc_end.pos_cnum - loc_end.pos_bol in
    if (not v) then
      if ch_start >= ch_end then
	"Character " ^ (string_of_int ch_start)
      else 
        "Characters " ^ (string_of_int ch_start)
         ^ "-" ^ (string_of_int ch_end)
    else
       "File \"" ^ loc_start.pos_fname ^ "\", " ^
       (if loc_start.pos_lnum = loc_end.pos_lnum then
          if ch_start >= ch_end then
            "line " ^ (string_of_int loc_start.pos_lnum)
            ^ ", character " ^ (string_of_int ch_start)
          else
            "line " ^ (string_of_int loc_start.pos_lnum)
            ^ ", characters " ^ (string_of_int ch_start)
            ^ "-" ^ (string_of_int ch_end) 
        else
          "line " ^ (string_of_int loc_start.pos_lnum)
          ^ ", character " ^ (string_of_int ch_start)
          ^ " - line " ^ (string_of_int loc_end.pos_lnum)
          ^ ", character " ^ (string_of_int ch_end)))

let get_extent_string v ext =
  match get_extent v ext with
  | None -> ""
  | Some s -> s ^":\n"
      
(* Get the message to write from mess and ext. Verbose if v is true *)
let get_mess_from v prefix mess ext =
  (get_extent_string v ext) ^ prefix ^  mess ^ add_point_if_necessary mess

(* Print the message with the location of the error, and a point at the end if needed. *)
let display_input_error mess ext =
  print_endline (get_mess_from true "Error: " mess ext);
  exit 2

(* print a warning message with the location of the error, and a point at the end if needed *)

(*for interactive mode *)
let interactive_mode = ref false

let warning_list = ref []

let get_warning_list() =
  let result = !warning_list in
  warning_list := [];
  result

let input_warning mess ext =
  if !interactive_mode then
    warning_list := (mess, ext) :: (!warning_list)
  else
    print_endline (get_mess_from true "Warning: " mess ext)

(* raise InputError with unknown extent *)
let user_error mess =
  raise (InputError (mess, dummy_ext))

(* Helper functions to lex strings *)
    
let buf = Buffer.create 64
let start_pos = ref Lexing.dummy_pos
let end_pos = ref Lexing.dummy_pos

(* The position of the beginning of a string is just after the opening quotation mark *)
let set_start_pos lexbuf = start_pos := Lexing.lexeme_end_p lexbuf
(* The position of the end of a string is just before the closing quotation mark *)
let set_end_pos lexbuf = end_pos := Lexing.lexeme_start_p lexbuf
    
let clear_buffer () =
  Buffer.reset buf

let get_string () =
  let s = Buffer.contents buf in
  clear_buffer ();
  (s, (!start_pos, !end_pos))

let add_char c =
  Buffer.add_char buf c

let char_backslash = function
    'n' -> '\n'
  | 't' -> '\t'
  | 'b' -> '\b'
  | 'r' -> '\r'
  | c -> c

