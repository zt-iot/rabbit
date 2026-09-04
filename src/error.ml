module type E = sig
  (** Type of error *)
  type error

  (** Error printer *)
  val print_error : error Sig.printer
end

module type S = sig
  include E

  exception Error of error Location.located

  val error : loc:Location.t -> error -> 'exn
end

module Make(E : E) : S with type error := E.error = struct
  include E

  exception Error of E.error Location.located

  (** [error ~loc err] raises the given runtime error. *)
  let error ~loc err = Stdlib.raise @@ Error (Location.locate ~loc err)
end
