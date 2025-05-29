type t = string * int

let cntr = ref 0

let global s = s, 0

let local s =
  incr cntr;
  s, !cntr

let name (s, i) =
  if i = 0 then s
  else Printf.sprintf "%s__%d" s i
