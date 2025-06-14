type ident = string
type t = ident

module Set : Set.S with type elt = ident
