module StringMap = Map.Make(String)

type 'a string_map = 'a StringMap.t


let pp_string_map pp_value fmt map =
  let pp_binding fmt (key, value) =
    Format.fprintf fmt "@[<hov 2>%S ->@ %a@]" key pp_value value
  in
  let bindings = StringMap.bindings map in
  Format.fprintf fmt "@[<hv 0>{@;<0 2>@[<v 0>%a@]@;<0 0>}@]"
    (Format.pp_print_list
       ~pp_sep:(fun fmt () -> Format.fprintf fmt ";@;<1 0>")
       pp_binding)
    bindings

let equal_string_map equal_value map1 map2 =
  StringMap.equal equal_value map1 map2