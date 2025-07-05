type ident = string [@@deriving show]
type t = ident [@@deriving show]

module Set = Set.Make(struct
    type t = ident
    let compare = compare
  end)
