(* we assign an `int` to each `Ident.t` to ensure that each variable in a Rabbit program has a unique name *)
type t = string * int [@@deriving show, eq]

let compare ((s1, i1) : t) ((s2, i2) : t) =
  let cmp_str = String.compare s1 s2 in
  if cmp_str <> 0 then cmp_str
  else Int.compare i1 i2


module IdentOrd = struct
  type t = string * int [@@deriving show]
  let compare = compare
end


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
