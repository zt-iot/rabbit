open Ocamlbuild_plugin;;

dispatch 
    ( function 
    | After_rules -> pdep ["link"] "linkdep" (fun param -> [param])
    | _           -> ()
     )
  
