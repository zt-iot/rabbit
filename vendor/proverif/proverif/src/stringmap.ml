module StringComp = struct
   type t = string
   let compare = compare
end

module StringMap = Map.Make(StringComp)
