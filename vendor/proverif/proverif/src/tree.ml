(* This file is a modified version of the file stdlib/map.ml of the official 
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
    type key
    type +'a t
    val empty: 'a t
    val is_empty: 'a t -> bool
    val update: key -> ('a option -> 'a option) -> 'a t -> 'a t
    val singleton: key -> 'a -> 'a t

    val exists_leq : (key list -> 'a -> bool) -> key -> key list -> 'a t -> bool

    val iter : ('a -> unit) -> 'a t -> unit
    val iter_geq : ('a -> unit) -> ('a -> unit) -> key -> 'a t -> unit
    val update_all : ('a -> 'a option) -> 'a t -> 'a t
  end

module Make(Ord: OrderedType) =
  struct

    type key = Ord.t

    let compare_lex (t1,t2) (t1',t2') =
      let c = Ord.compare_fst t1 t1' in
      if c = 0
      then Ord.compare_snd t2 t2'
      else c

    type 'a t =
        Empty
      | Node of {l:'a t; v:key; d:'a; r:'a t; h:int}

    let height = function
        Empty -> 0
      | Node {h} -> h

    let create l x d r =
      let hl = height l and hr = height r in
      Node{l; v=x; d; r; h=(if hl >= hr then hl + 1 else hr + 1)}

    let singleton x d = Node{l=Empty; v=x; d; r=Empty; h=1}

    let bal l x d r =
      let hl = match l with Empty -> 0 | Node {h} -> h in
      let hr = match r with Empty -> 0 | Node {h} -> h in
      if hl > hr + 2 then begin
        match l with
          Empty -> invalid_arg "Map.bal"
        | Node{l=ll; v=lv; d=ld; r=lr} ->
            if height ll >= height lr then
              create ll lv ld (create lr x d r)
            else begin
              match lr with
                Empty -> invalid_arg "Map.bal"
              | Node{l=lrl; v=lrv; d=lrd; r=lrr}->
                  create (create ll lv ld lrl) lrv lrd (create lrr x d r)
            end
      end else if hr > hl + 2 then begin
        match r with
          Empty -> invalid_arg "Map.bal"
        | Node{l=rl; v=rv; d=rd; r=rr} ->
            if height rr >= height rl then
              create (create l x d rl) rv rd rr
            else begin
              match rl with
                Empty -> invalid_arg "Map.bal"
              | Node{l=rll; v=rlv; d=rld; r=rlr} ->
                  create (create l x d rll) rlv rld (create rlr rv rd rr)
            end
      end else
        Node{l; v=x; d; r; h=(if hl >= hr then hl + 1 else hr + 1)}

    let empty = Empty

    let is_empty = function Empty -> true | _ -> false

    let rec min_binding = function
        Empty -> raise Not_found
      | Node {l=Empty; v; d} -> (v, d)
      | Node {l} -> min_binding l

    let rec remove_min_binding = function
        Empty -> invalid_arg "Map.remove_min_elt"
      | Node {l=Empty; r} -> r
      | Node {l; v; d; r} -> bal (remove_min_binding l) v d r

    let merge t1 t2 =
      match (t1, t2) with
        (Empty, t) -> t
      | (t, Empty) -> t
      | (_, _) ->
          let (x, d) = min_binding t2 in
          bal t1 x d (remove_min_binding t2)

    let rec update x f = function
        Empty ->
          begin match f None with
          | None -> Empty
          | Some data -> Node{l=Empty; v=x; d=data; r=Empty; h=1}
          end
      | Node {l; v; d; r; h} as m ->
          let c = compare_lex x v in
          if c = 0 then begin
            match f (Some d) with
            | None -> merge l r
            | Some data ->
                if d == data then m else Node{l; v=x; d=data; r; h}
          end else if c < 0 then
            let ll = update x f l in
            if l == ll then m else bal ll v d r
          else
            let rr = update x f r in
            if r == rr then m else bal l v d rr

    let rec iter f = function
        Empty -> ()
      | Node {l; v; d; r} ->
          iter f l; f d; iter f r

    let rec iter_geq_generic f k = function
      | Empty -> ()
      | Node {l; v; d; r} ->
          let c = compare_lex v k in
          if c = 0
          then (f d; iter f r)
          else if c < 0
          then iter_geq_generic f k r
          else (f d; iter f r; iter_geq_generic f k l)

    let rec iter_geq f_ge f_eq ((k1,k2) as k) = function
      | Empty -> ()
      | Node {l; v = (v1,v2); d; r} ->
          let c1 = Ord.compare_fst v1 k1 in
          if c1 = 0
          then
            let c2 = Ord.compare_snd v2 k2 in
            if c2 = 0
            then (f_eq d; iter_geq f_ge f_eq k r)
            else if c2 < 0
            then iter_geq f_ge f_eq k r
            else (f_eq d; iter_geq_generic f_eq k l; iter_geq f_ge f_eq k r)
          else if c1 < 0
          then iter_geq f_ge f_eq k r
          else (f_ge d; iter f_ge r; iter_geq f_ge f_eq k l)

    let rec exists p = function
        Empty -> false
      | Node {l; v; d; r} -> p d || exists p l || exists p r

    (* [exists_leq_generic p k t] returns true iff there exists a key [k'] and its
       data [d'] in [t] such that [k' <= k] and [p d' = true]*)
    let rec exists_leq_generic p k = function
      | Empty -> false
      | Node {l; v; d; r} ->
          let c = compare_lex v k in
          if c = 0
          then p d || exists p l
          else if c < 0
          then p d || exists p l || exists_leq_generic p k r
          else exists_leq_generic p k l

    (* [remove_until fst_k [k_1;...;k_n]] removes from the list all keys whose first
       attribute is bigger than fst_k. More formally, the function returns a pair [eq_op,l]
       where:
        - [eq_op = Some(snd(k_i),[k_{i+1};...;k_n])] and [ l = [k_i;...;k_n]] if [fst(k_i) = fst_k]
        - otherwise [eq_op = None] and [ l = [k_i;...;k_n]] and [i] is the smallest
          index such that [fst(k_i) <= fst_k]

      We assume the following properties on [k_1;...;k_n]:
       - i <> j implies fst k_i <> fst k_j
       - i < j implies fst k_i > fst k_j
       - fst k > fst k_1
    *)
    let rec remove_until v1 = function
      | [] -> None, []
      | ((v1',v2')::q) as l ->
          let c = Ord.compare_fst v1 v1' in
          if c = 0
          then Some(v2',q),l
          else if c < 0
          then remove_until v1 q
          else None, l

    let rec exists_aux p k_list t = match t, k_list with
      | _, []
      | Empty, _ -> false
      | Node {l; v = (v1,v2); d; r}, (k1,k2)::q ->
          match remove_until v1 k_list with
            | None, k_list'' ->
                (* all k'' in k_list'' satisfy fst k'' <= v1 *)
                exists_aux p k_list'' l || exists_aux p k_list r
            | Some(k2',k_list'), k_list'' ->
                (* all k'' in k_list' and k_list'' satisfy fst k'' <= v1 *)
                (Ord.compare_snd v2 k2' <= 0 && p k_list' d) ||
                exists_aux p k_list'' l ||
                exists_aux p k_list r

    (* [exists_leq p k [k_1;...;k_n] t] is true if and only if there exists a key [k'] and
       its data [d'] in [t] such that:
        - either fst k' = fst k && snd k' <= snd k && p [k_1;...;k_n] d'
        - or fst k' < fst k && there exists i such that
            fst k' = fst k_i && snd k' <= snd k_i && p [k_(i+1);...;k_n] d'

       We assume the following properties on [k_1;...;k_n]:
        - i <> j implies fst k_i <> fst k_j
        - i < j implies fst k_i > fst k_j
        - fst k > fst k_1
    *)
    let rec exists_leq p ((k1,k2) as k) k_list = function
      | Empty -> false
      | Node {l; v = (v1,v2); d; r} ->
          let c1 = Ord.compare_fst v1 k1 in
          if c1 = 0
          then
            let c2 = Ord.compare_snd v2 k2 in
            if c2 = 0
            then
              p k_list d || (* Since k = v, we need to check if the predicate holds on k_list and d *)
              exists_leq p k k_list l
            else if c2 < 0
            then
              p k_list d ||
              exists_leq_generic (p k_list) k r || (* We need to look in the right side of the tree for the keys smaller than k (in the lexicographic sense) *)
              exists_leq p k k_list l
            else exists_leq p k k_list l
          else if c1 < 0
          then
            match remove_until v1 k_list with
              | None, k_list'' ->
                  (* all k'' in k_list'' satisfy fst k'' <= v1 *)
                  exists_aux p k_list'' l || exists_leq p k k_list r
              | Some(k2',k_list'),k_list'' ->
                  (* all k'' in k_list' and k_list'' satisfy fst k'' <= v1 *)
                  (Ord.compare_snd v2 k2' <= 0 && p k_list' d) ||
                  exists_aux p k_list'' l ||
                  exists_leq p k k_list r
          else exists_leq p k k_list l

    (* Beware: those two functions assume that the added k is *strictly*
       smaller (or bigger) than all the present keys in the tree; it
       does not test for equality with the current min (or max) key.
       Indeed, they are only used during the "join" operation which
       respects this precondition.
    *)

    let rec add_min_binding k x = function
      | Empty -> singleton k x
      | Node {l; v; d; r} ->
        bal (add_min_binding k x l) v d r

    let rec add_max_binding k x = function
      | Empty -> singleton k x
      | Node {l; v; d; r} ->
        bal l v d (add_max_binding k x r)

    (* Same as create and bal, but no assumptions are made on the
       relative heights of l and r. *)

    let rec join l v d r =
      match (l, r) with
        (Empty, _) -> add_min_binding v d r
      | (_, Empty) -> add_max_binding v d l
      | (Node{l=ll; v=lv; d=ld; r=lr; h=lh},
         Node{l=rl; v=rv; d=rd; r=rr; h=rh}) ->
          if lh > rh + 2 then bal ll lv ld (join lr v d r) else
          if rh > lh + 2 then bal (join l v d rl) rv rd rr else
          create l v d r

    (* Merge two trees l and r into one.
       All elements of l must precede the elements of r.
       No assumption on the heights of l and r. *)

    let concat t1 t2 =
      match (t1, t2) with
        (Empty, t) -> t
      | (t, Empty) -> t
      | (_, _) ->
          let (x, d) = min_binding t2 in
          join t1 x d (remove_min_binding t2)

    (* [update_all f m] returns a map such that for all bindings [k -> d],
          if [f d = None] then the binding is removed
          if [f d = Some d'] then the binding is replaced and [k] is associated to [d'].*)
    let rec update_all p = function
      | Empty -> Empty
      | Node {l; v; d; r} ->
          let l' = update_all p l in
          let r' = update_all p r in
          match p d with
            | None -> concat l' r'
            | Some d' -> join l' v d' r'
end


module type OrderedTypeOne =
  sig
    type t

    val compare : t -> t -> int
  end

module type SOne =
  sig
    type key
    type +'a t
    val empty: 'a t
    val is_empty: 'a t -> bool
    val update: key -> ('a option -> 'a option) -> 'a t -> 'a t
    val singleton: key -> 'a -> 'a t
    val find_opt: key -> 'a t -> 'a option

    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val update_all : ('a -> 'a option) -> 'a t -> 'a t
  end

module MakeOne(Ord: OrderedTypeOne) =
  struct

    type key = Ord.t

    type 'a t =
        Empty
      | Node of {l:'a t; v:key; d:'a; r:'a t; h:int}

    let height = function
        Empty -> 0
      | Node {h} -> h

    let create l x d r =
      let hl = height l and hr = height r in
      Node{l; v=x; d; r; h=(if hl >= hr then hl + 1 else hr + 1)}

    let singleton x d = Node{l=Empty; v=x; d; r=Empty; h=1}

    let bal l x d r =
      let hl = match l with Empty -> 0 | Node {h} -> h in
      let hr = match r with Empty -> 0 | Node {h} -> h in
      if hl > hr + 2 then begin
        match l with
          Empty -> invalid_arg "Map.bal"
        | Node{l=ll; v=lv; d=ld; r=lr} ->
            if height ll >= height lr then
              create ll lv ld (create lr x d r)
            else begin
              match lr with
                Empty -> invalid_arg "Map.bal"
              | Node{l=lrl; v=lrv; d=lrd; r=lrr}->
                  create (create ll lv ld lrl) lrv lrd (create lrr x d r)
            end
      end else if hr > hl + 2 then begin
        match r with
          Empty -> invalid_arg "Map.bal"
        | Node{l=rl; v=rv; d=rd; r=rr} ->
            if height rr >= height rl then
              create (create l x d rl) rv rd rr
            else begin
              match rl with
                Empty -> invalid_arg "Map.bal"
              | Node{l=rll; v=rlv; d=rld; r=rlr} ->
                  create (create l x d rll) rlv rld (create rlr rv rd rr)
            end
      end else
        Node{l; v=x; d; r; h=(if hl >= hr then hl + 1 else hr + 1)}

    let empty = Empty

    let is_empty = function Empty -> true | _ -> false

    let rec add x data = function
        Empty ->
          Node{l=Empty; v=x; d=data; r=Empty; h=1}
      | Node {l; v; d; r; h} as m ->
          let c = Ord.compare x v in
          if c = 0 then
            if d == data then m else Node{l; v=x; d=data; r; h}
          else if c < 0 then
            let ll = add x data l in
            if l == ll then m else bal ll v d r
          else
            let rr = add x data r in
            if r == rr then m else bal l v d rr

    let rec min_binding = function
        Empty -> raise Not_found
      | Node {l=Empty; v; d} -> (v, d)
      | Node {l} -> min_binding l

    let rec remove_min_binding = function
        Empty -> invalid_arg "Map.remove_min_elt"
      | Node {l=Empty; r} -> r
      | Node {l; v; d; r} -> bal (remove_min_binding l) v d r

    let merge t1 t2 =
      match (t1, t2) with
        (Empty, t) -> t
      | (t, Empty) -> t
      | (_, _) ->
          let (x, d) = min_binding t2 in
          bal t1 x d (remove_min_binding t2)

    let rec update x f = function
        Empty ->
          begin match f None with
          | None -> Empty
          | Some data -> Node{l=Empty; v=x; d=data; r=Empty; h=1}
          end
      | Node {l; v; d; r; h} as m ->
          let c = Ord.compare x v in
          if c = 0 then begin
            match f (Some d) with
            | None -> merge l r
            | Some data ->
                if d == data then m else Node{l; v=x; d=data; r; h}
          end else if c < 0 then
            let ll = update x f l in
            if l == ll then m else bal ll v d r
          else
            let rr = update x f r in
            if r == rr then m else bal l v d rr

    let rec iter f = function
        Empty -> ()
      | Node {l; v; d; r} ->
          iter f l; f v d; iter f r

    let rec exists p = function
        Empty -> false
      | Node {l; v; d; r} -> p d || exists p l || exists p r

    let rec find_opt x = function
        Empty ->
          None
      | Node {l; v; d; r} ->
          let c = Ord.compare x v in
          if c = 0 then Some d
          else find_opt x (if c < 0 then l else r)

    (* Beware: those two functions assume that the added k is *strictly*
       smaller (or bigger) than all the present keys in the tree; it
       does not test for equality with the current min (or max) key.
       Indeed, they are only used during the "join" operation which
       respects this precondition.
    *)

    let rec add_min_binding k x = function
      | Empty -> singleton k x
      | Node {l; v; d; r} ->
        bal (add_min_binding k x l) v d r

    let rec add_max_binding k x = function
      | Empty -> singleton k x
      | Node {l; v; d; r} ->
        bal l v d (add_max_binding k x r)

    (* Same as create and bal, but no assumptions are made on the
       relative heights of l and r. *)

    let rec join l v d r =
      match (l, r) with
        (Empty, _) -> add_min_binding v d r
      | (_, Empty) -> add_max_binding v d l
      | (Node{l=ll; v=lv; d=ld; r=lr; h=lh},
         Node{l=rl; v=rv; d=rd; r=rr; h=rh}) ->
          if lh > rh + 2 then bal ll lv ld (join lr v d r) else
          if rh > lh + 2 then bal (join l v d rl) rv rd rr else
          create l v d r

    (* Merge two trees l and r into one.
       All elements of l must precede the elements of r.
       No assumption on the heights of l and r. *)

    let concat t1 t2 =
      match (t1, t2) with
        (Empty, t) -> t
      | (t, Empty) -> t
      | (_, _) ->
          let (x, d) = min_binding t2 in
          join t1 x d (remove_min_binding t2)

    let rec update_all p = function
      | Empty -> Empty
      | Node {l; v; d; r} ->
          let l' = update_all p l in
          let r' = update_all p r in
          match p d with
            | None -> concat l' r'
            | Some d' -> join l' v d' r'
end
