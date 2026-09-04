type error = ..

let printers : error Sig.printer list ref = ref []

let add_printer p = printers := p :: !printers

exception Error of error Location.located

exception Use_other_printers

let raise ~loc err = Stdlib.raise @@ Error (Location.locate ~loc err)

let use_other_printers () = Stdlib.raise Use_other_printers

let print : error Location.located Sig.printer = fun e ppf->
  Format.fprintf ppf "%a: %a"
    (fun ppf x -> Location.print x ppf) e.loc
    (fun ppf x ->
       (let rec loop = function
           | [] -> failwith "No printer for this error"
           | (p : error Sig.printer)::ps -> try p x ppf with Use_other_printers -> loop ps
        in
        loop !printers)) e.data
