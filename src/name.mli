type ident = string [@@deriving show]
type t = ident [@@deriving show]

module Set : Set.S with type elt = ident
