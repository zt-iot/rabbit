module StringMap : Map.S with type key = string



(*
empty	The empty map
add k v m	Add key k with value v to map m
find k m / find_opt	Get value for key k
mem k m	Check if key k is in the map
remove k m	Remove key k
iter (fun k v -> ...) m	Iterate over key-value pairs
fold (fun k v acc -> ...) m a	Fold over entries
bindings m	Return list of (key * value) pairs
*)
type 'a string_map = 'a StringMap.t

val pp_string_map : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a string_map -> unit
val equal_string_map : ('a -> 'a -> bool) -> 'a string_map -> 'a string_map -> bool