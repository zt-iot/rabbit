type name = Name.ident
type ident = Ident.t

module Index : sig
  type t = private (int * int) list

  (** [add i n] for $i + n$ *)
  val add : t -> int -> t

  (** [push i n] for $i_n$ *)
  val push : t -> int -> t

  val to_string : t -> string
end = struct
  type t = (int * int) list

  let zero = [ 0, 0 ]

  let add i k =
    match i with
    | [] -> assert false
    | (n, j) :: i' -> (n, j + k) :: i'
  ;;

  let push i n = (n, 0) :: i

  let to_string i =
    String.concat "__" @@ List.map (fun (a, b) -> Printf.sprintf "%d.%d" a b) i
  ;;
end

type fact = Typed.fact

type update =
  { register : Typed.expr option (* None: \rho *)
  ; mutable_overrides : (Ident.t * Typed.expr) list
  }

type edge =
  { source : Index.t
  ; source_env : Env.t
  ; pre : fact list
  ; update : update
  ; tag : fact list
  ; post : fact list
  ; target : Index.t
  ; target_env : Env.t
  }

type graph = edge list

let evar env id =
  Typed.
    { env
    ; loc = Location.nowhere
    ; desc = Ident { id; desc = Var (Loc (snd id)); param = None }
    }
;;

(* <\Gamma |- c>i *)
let rec graph_cmd ~process i (c : Typed.cmd) : graph * Index.t =
  let env = c.env in
  let update_unit =
    { register = Some Typed.{ env; loc = Location.nowhere; desc = Unit }
    ; mutable_overrides = []
    }
  in
  let update_id = { register = None; mutable_overrides = [] } in
  let fact env desc : Typed.fact = Typed.{ env; desc; loc = Location.nowhere } in
  match c.desc with
  | Skip ->
      let i_1 = Index.add i 1 in
      ( [ { source = i (* transition_from *)
          ; source_env = env
          ; pre = [] (* transition_pre *)
          ; update = update_unit (* transitino_state_transition *)
          ; tag = [] (* transition_label *)
          ; post = [] (* transition_post *)
          ; target = i_1 (* transition_to *)
          ; target_env = env
          }
        ]
      , i_1 )
  | Sequence (c1, c2) ->
      let g1, j = graph_cmd ~process i c1 in
      let g2, k = graph_cmd ~process j c2 in
      g1 @ g2, k
  | Put fs ->
      let i_1 = Index.add i 1 in
      ( [ { source = i
          ; source_env = env
          ; pre = []
          ; update = update_unit
          ; tag = []
          ; post = fs
          ; target = i_1
          ; target_env = env
          }
        ]
      , i_1 )
  | Let (x, e, c) ->
      (* var x := e in c *)
      let i_1 = Index.add i 1 in
      let g, j = graph_cmd ~process i_1 c in
      let j_1 = Index.add j 1 in
      ( { source = i
        ; source_env = env
        ; pre = []
        ; update = { update_unit with mutable_overrides = [ x, e ] }
        ; tag = []
        ; post = []
        ; target = i_1
        ; target_env = c.env
        }
        :: { source = j
           ; source_env = c.env
           ; pre = []
           ; update = update_id
           ; tag = []
           ; post = []
           ; target = j_1
           ; target_env = env
           }
        :: g
      , j_1 )
  | Assign (Some x, e) ->
      let i_1 = Index.add i 1 in
      ( [ { source = i
          ; source_env = env
          ; pre = []
          ; update = { update_unit with mutable_overrides = [ x, e ] }
          ; tag = []
          ; post = []
          ; target = i_1
          ; target_env = env
          }
        ]
      , i_1 )
  | Assign (None, _e) ->
      (* XXX e is lost... *)
      let i_1 = Index.add i 1 in
      ( [ { source = i
          ; source_env = env
          ; pre = []
          ; update = update_unit
          ; tag = []
          ; post = []
          ; target = i_1
          ; target_env = env
          }
        ]
      , i_1 )
  | Event facts ->
      let i_1 = Index.add i 1 in
      ( [ { source = i
          ; source_env = env
          ; pre = []
          ; update = update_unit
          ; tag = facts
          ; post = []
          ; target = i_1
          ; target_env = env
          }
        ]
      , i_1 )
  | Return e ->
      let i_1 = Index.add i 1 in
      ( [ { source = i
          ; source_env = env
          ; pre = []
          ; update = { register = Some e; mutable_overrides = [] }
          ; tag = []
          ; post = []
          ; target = i_1
          ; target_env = env
          }
        ]
      , i_1 )
  | New (x, eopt, c) ->
      let i_1 = Index.add i 1 in
      let g, j = graph_cmd ~process i_1 c in
      let j_1 = Index.add j 1 in
      ( { source = i
        ; source_env = env
        ; pre = [ fact c.env @@ Fresh (evar c.env x) ]
        ; update = update_unit
        ; tag = []
        ; post = []
        ; target = i_1
        ; target_env = c.env
        }
        :: { source = j
           ; source_env = c.env
           ; pre = []
           ; update = update_id
           ; tag = []
           ; post =
               (match eopt with
                | None -> []
                | Some (s, es) ->
                    [ fact c.env
                      @@ Structure
                           { name = s; process; address = evar c.env x; args = es }
                    ])
           ; target = j_1
           ; target_env = env
           }
        :: g
      , j_1 )
  | Get (xs, e, s, c) ->
      (* [let x1,..,xn := e.S in c] *)
      let i_1 = Index.add i 1 in
      let g, j = graph_cmd ~process i_1 c in
      let j_1 = Index.add j 1 in
      let pre_and_post : fact list =
        [ fact env
          @@ Structure { name = s; process; address = e; args = List.map (evar c.env) xs }
        ]
      in
      ( { source = i
        ; source_env = env
        ; pre = pre_and_post
        ; update = update_unit
        ; tag = []
        ; post = pre_and_post
        ; target = i_1
        ; target_env = c.env
        }
        :: { source = j
           ; source_env = c.env
           ; pre = []
           ; update = update_id
           ; tag = []
           ; post = []
           ; target = j_1
           ; target_env = env
           }
        :: g
      , j_1 )
  | Del (e, s) ->
      let i_1 = Index.add i 1 in
      let arity =
        match Env.find_fact_opt env s with
        | Some (Structure, Some arity) -> arity
        | _ -> assert false (* XXX *)
      in
      let xs =
        List.init arity
        @@ fun i ->
        let id = Ident.local (Printf.sprintf "x%d" i) in
        Typed.
          { env (* XXX vars are not defied in env *)
          ; loc = Location.nowhere
          ; desc = Ident { id; desc = Var (Loc (snd id)); param = None }
          }
      in
      ( [ { source = i
          ; source_env = env
          ; pre = [ fact env @@ Structure { name = s; process; address = e; args = xs } ]
          ; update = update_unit
          ; tag = []
          ; post = []
          ; target = i_1
          ; target_env = env
          }
        ]
      , i_1 )
  | Case cases ->
      let i_1 = Index.add i 1 in
      let es =
        List.concat
        @@ List.mapi
             (fun j (case : Typed.case) ->
                (* XXX case.cmd.env == case.fresh @ env *)
                let ij = Index.push i j in
                let gj, bj (* bold j *) = graph_cmd ~process ij case.cmd in
                { source = i
                ; source_env = env
                ; pre = case.facts
                ; update = update_unit
                ; tag = []
                ; post = []
                ; target = ij
                ; target_env = case.cmd.env (* XXX == case.fresh @ env *)
                }
                :: { source = bj
                   ; source_env = case.cmd.env
                   ; pre = []
                   ; update = update_id
                   ; tag = []
                   ; post = []
                   ; target = i_1
                   ; target_env = env
                   }
                :: gj)
             cases
      in
      es, i_1
  | While (cases, cases') ->
      let i_1 = Index.add i 1 in
      let i_2 = Index.add i 2 in
      let n = List.length cases in
      let es =
        ({ source = i
         ; source_env = env
         ; pre = []
         ; update = update_unit
         ; tag = [ fact env @@ Loop { mode = In; process; index = Index.to_string i } ]
         ; post = []
         ; target = i_1
         ; target_env = env
         }
         :: List.concat
              (List.mapi
                 (fun j (case : Typed.case) ->
                    (* XXX case.cmd.env == case.fresh @ env *)
                    let i_1j = Index.push i_1 j in
                    let gj, bj (* bold j *) = graph_cmd ~process i_1j case.cmd in
                    { source = i_1
                    ; source_env = env
                    ; pre = case.facts
                    ; update = update_unit
                    ; tag = []
                    ; post = []
                    ; target = i_1j
                    ; target_env = case.cmd.env (* XXX == case.fresh @ env *)
                    }
                    :: { source = bj
                       ; source_env = case.cmd.env
                       ; pre = []
                       ; update = update_unit
                       ; tag =
                           [ fact case.cmd.env
                             @@ Loop { mode = Back; process; index = Index.to_string i }
                           ]
                       ; post = []
                       ; target = i_1
                       ; target_env = env
                       }
                    :: gj)
                 cases))
        @ List.concat
            (List.mapi
               (fun j (case : Typed.case) ->
                  (* XXX case.cmd.env == case.fresh @ env *)
                  let i_1jn = Index.push i_1 (j + n) in
                  let gj, bj (* bold j *) = graph_cmd ~process i_1jn case.cmd in
                  { source = i_1
                  ; source_env = env
                  ; pre = case.facts
                  ; update = update_unit
                  ; tag = []
                  ; post = []
                  ; target = i_1jn
                  ; target_env = case.cmd.env (* XXX == case.fresh @ env *)
                  }
                  :: { source = bj
                     ; source_env = case.cmd.env
                     ; pre = []
                     ; update = update_id
                     ; tag =
                         [ fact case.cmd.env
                           @@ Loop { mode = Out; process; index = Index.to_string i }
                         ]
                     ; post = []
                     ; target = i_2
                     ; target_env = env
                     }
                  :: gj)
               cases')
      in
      es, i_2
;;
