type ident = string

module Set = Set.Make(struct
    type t = ident
    let compare = compare
  end)
