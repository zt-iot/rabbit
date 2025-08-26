type t = string * int

let cntr = ref 0

let global s = s, 0

let local s =
  incr cntr;
  s, !cntr

let is_global id = snd id = 0

let to_string (s, i) =
  if i = 0 then s
  else Printf.sprintf "%s__%d" s i

let print id ppf = Format.fprintf ppf "%s" (fst id)

let prefix s (name, idx) =
  assert (s <> "");
  s ^ name, idx

module Set = Set.Make(struct
    type nonrec t = t
    let compare = compare
  end)
