type ident = string
type t = ident

module Set = Set.Make(struct
    type t = ident
    let compare = compare
  end)
