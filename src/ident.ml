type t = string * int [@@deriving show]

let cntr = ref 0

let global s = s, 0

let local s =
  incr cntr;
  s, !cntr

(* Extracts the string part of an Ident.t *)
let string_part (s, _) = s

let name (s, i) =
  if i = 0 then s
  else Printf.sprintf "%s__%d" s i

let print id ppf = Format.fprintf ppf "%s" (fst id)

let to_string id = fst id ^ "__" ^ string_of_int (snd id)
