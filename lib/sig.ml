type 'a printer = 'a -> Format.formatter -> unit

module type ERROR = sig
  (** Type of error *)
  type error

  (** Exception with the location information *)
  exception Error of error Location.located

  (** Raise an Error *)
  val error : loc:Location.t -> error -> 'error

  (** Error printer *)
  val print_error : error printer
end
