type error = ..

val add_printer : error Sig.printer -> unit

exception Error of error Location.located

val raise : loc:Location.t -> error -> 'exn

val use_other_printers : unit -> 'a

val print : error Location.located Sig.printer
