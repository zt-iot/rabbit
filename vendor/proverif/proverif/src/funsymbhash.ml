open Types

module HashTypeSymbol =
  struct
    type t = funsymb
    let equal = (==)

    let hash f = Hashtbl.hash (f.f_name,f.f_type,f.f_cat,f.f_initial_cat,f.f_private)
  end

module HashtblSymbol = Hashtbl.Make(HashTypeSymbol)
