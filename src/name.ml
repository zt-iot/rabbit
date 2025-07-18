type ident = string [@@deriving show, eq]
type t = ident [@@deriving show, eq]

module Set = Set.Make(struct
    type t = ident
    let compare = compare
  end)
