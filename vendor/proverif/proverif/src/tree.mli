(* This file is a modified version of the file stdlib/map.mli of the official 
   distribution of OCaml.
   The original file is by Xavier Leroy, projet Cristal, INRIA Rocquencourt 
   Copyright 1996 Institut National de Recherche en Informatique et en 
   Automatique.
   Modified by Vincent Cheval and Bruno Blanchet, April 2020. *)

module type OrderedType =
  sig
    type t_fst
    type t_snd
    type t = t_fst * t_snd

    val compare_fst : t_fst -> t_fst -> int
    val compare_snd : t_snd -> t_snd -> int
  end

module type S =
  sig

    (** The type of the map keys. *)
    type key

    (** The type of maps from type [key] to type ['a]. *)
    type (+'a) t


    (** The empty map. *)
    val empty: 'a t


    (** Test whether a map is empty or not. *)
    val is_empty: 'a t -> bool

    (** [update x f m] returns a map containing the same bindings as
        [m], except for the binding of [x]. Depending on the value of
        [y] where [y] is [f (find_opt x m)], the binding of [x] is
        added, removed or updated. If [y] is [None], the binding is
        removed if it exists; otherwise, if [y] is [Some z] then [x]
        is associated to [z] in the resulting map.  If [x] was already
        bound in [m] to a value that is physically equal to [z], [m]
        is returned unchanged (the result of the function is then
        physically equal to [m]).
    *)
    val update: key -> ('a option -> 'a option) -> 'a t -> 'a t

    (** [singleton x y] returns the one-element map that contains a binding [y]
        for [x].
     *)
    val singleton: key -> 'a -> 'a t

    (***********************************************************)
    (* Modified and new functions compared to OCaml file map.ml *)

    (** [exists_leq p k [k_1;...;k_n] t] is true if and only if there exists a key [k'] and
       its data [d'] in [t] such that:
        - either fst k' = fst k && snd k' <= snd k && p [k_1;...;k_n] d'
        - or fst k' < fst k && there exists i such that
            fst k' = fst k_i && snd k' <= snd k_i && p [k_(i+1);...;k_n] d'

       We assume the following properties on [k_1;...;k_n]:
        - i <> j implies fst k_i <> fst k_j
        - i < j implies fst k_i > fst k_j
        - fst k > fst k_1
    *)
    val exists_leq : (key list -> 'a -> bool) -> key -> key list -> 'a t -> bool

    (** [iter f m] applies [f] to all bindings in the map [m].
       [f] receives the associated value as argument. The bindings are passed to [f]
       in increasing order with respect to the ordering over the type of the keys. *)
    val iter : ('a -> unit) -> 'a t -> unit

    (** [iter_geq f_ge f_eq k m] applies:
          - [f_eq] to all bindings in [m] with a key [k' >= k] such that [fst k' = fst k].
          - [f_ge] to all bindings in [m] with a key [k' >= k] such that [fst k' > fst k].

        No specific order on the applications of the functions w.r.t. the keys in the tree.
    *)
    val iter_geq : ('a -> unit) -> ('a -> unit) -> key -> 'a t -> unit

    (* [update_all f m] returns a map such that for all bindings [k -> d],
          if [f d = None] then the binding is removed
          if [f d = Some d'] then the binding is replaced and [k] is associated to [d'].*)
    val update_all : ('a -> 'a option) -> 'a t -> 'a t
  end

module Make (Ord : OrderedType) : S with type key = Ord.t
(** Functor building an implementation of the map structure
   given a totally ordered type. *)


module type OrderedTypeOne =
  sig
    type t

    val compare : t -> t -> int
  end

module type SOne =
  sig

    (** The type of the map keys. *)
    type key

    (** The type of maps from type [key] to type ['a]. *)
    type (+'a) t


    (** The empty map. *)
    val empty: 'a t


    (** Test whether a map is empty or not. *)
    val is_empty: 'a t -> bool

    (** [update x f m] returns a map containing the same bindings as
        [m], except for the binding of [x]. Depending on the value of
        [y] where [y] is [f (find_opt x m)], the binding of [x] is
        added, removed or updated. If [y] is [None], the binding is
        removed if it exists; otherwise, if [y] is [Some z] then [x]
        is associated to [z] in the resulting map.  If [x] was already
        bound in [m] to a value that is physically equal to [z], [m]
        is returned unchanged (the result of the function is then
        physically equal to [m]).
    *)
    val update: key -> ('a option -> 'a option) -> 'a t -> 'a t

    (** [singleton x y] returns the one-element map that contains a binding [y]
        for [x].
     *)
    val singleton: key -> 'a -> 'a t

    (** [find_first_opt f m], where [f] is a monotonically increasing function,
       returns an option containing the binding of [m] with the lowest key [k]
       such that [f k], or [None] if no such key exists.
       *)
    val find_opt: key -> 'a t -> 'a option

    (** [iter f m] applies [f] to all bindings in the map [m].
       [f] receives the key as first argument, and the associated value as second argument.
       The bindings are passed to [f] in increasing order with respect to the ordering
       over the type of the keys. *)
    val iter : (key -> 'a -> unit) -> 'a t -> unit

    (***********************************************************)
    (* New function compared to OCaml file map.ml *)

    (* [update_all f m] returns a map such that for all bindings [k -> d],
          if [f d = None] then the binding is removed
          if [f d = Some d'] then the binding is replaced and [k] is associated to [d'].*)
    val update_all : ('a -> 'a option) -> 'a t -> 'a t
  end

module MakeOne (Ord : OrderedTypeOne) : SOne with type key = Ord.t
(** Functor building an implementation of the map structure
   given a totally ordered type. *)
