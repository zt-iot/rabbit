module StringMap : Map.S with type key = string

type 'a string_map = 'a StringMap.t