type 'a q

val new_queue : unit -> 'a q

val add : 'a q -> 'a -> unit

val get : 'a q -> 'a option

val length : 'a q -> int

val exists : 'a q -> ('a -> bool) -> bool

val filter : 'a q -> ('a -> bool) -> unit

val iter : 'a q -> ('a -> unit) -> unit
