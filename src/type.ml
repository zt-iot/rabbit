type type_ =
  | TValue
  | TChannel
  | TParameter
  | TVar of type_var ref

and type_var =
  | Unbound of int
  | Link of type_

type callable_type =
  { argument_types : type_ list
  ; result_type : type_
  }

exception Cannot_unify of type_ * type_

let next_type_var = ref 0

let fresh_type () =
  let id = !next_type_var in
  incr next_type_var;
  let var = ref (Unbound id) in
  TVar var

let rec repr = function
  | TVar ({ contents = Link typ } as var) ->
      let typ = repr typ in
      var := Link typ;
      typ
  | typ -> typ

let unify typ1 typ2 =
  let typ1 = repr typ1 in
  let typ2 = repr typ2 in
  match typ1, typ2 with
  | TValue, TValue | TChannel, TChannel | TParameter, TParameter -> ()
  | TVar var1, TVar var2 when var1 == var2 -> ()
  | TVar ({ contents = Unbound _ } as var), typ
  | typ, TVar ({ contents = Unbound _ } as var) -> var := Link typ
  | _ -> raise (Cannot_unify (typ1, typ2))

let default_type typ =
  match repr typ with
  | TVar ({ contents = Unbound _ } as var) ->
      var := Link TValue;
      TValue
  | typ -> typ

let print_type typ ppf =
  match repr typ with
  | TValue -> Format.pp_print_string ppf "value"
  | TChannel -> Format.pp_print_string ppf "channel"
  | TParameter -> Format.pp_print_string ppf "parameter"
  | TVar { contents = Unbound id } -> Format.fprintf ppf "'%d" id
  | TVar { contents = Link _ } -> assert false
