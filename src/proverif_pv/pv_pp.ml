open Rabbit_proverif_pv_parse

type program = Pv_parser.program

open Pitptree

let fprintf = Format.fprintf

let pp_string = Format.pp_print_string

let pp_sep fmt sep =
  match sep with
  | "@," -> Format.pp_print_cut fmt ()
  | ";@ " -> fprintf fmt ";@ "
  | _ -> pp_string fmt sep

let pp_list ~sep f fmt xs =
  Format.pp_print_list
    ~pp_sep:(fun fmt () -> pp_sep fmt sep)
    f
    fmt
    xs

let ident (s, _) = s

let starts_with ~prefix s =
  let prefix_len = String.length prefix in
  String.length s >= prefix_len && String.sub s 0 prefix_len = prefix

let strip_prefix ~prefix s =
  String.sub s (String.length prefix) (String.length s - String.length prefix)

let join sep xs = String.concat sep xs

let pp_option fmt (name, value) =
  match value with
  | None -> pp_string fmt (ident name)
  | Some [v] -> fprintf fmt "%s = %s" (ident name) (ident v)
  | Some vs ->
      fprintf fmt "%s = {%s}" (ident name) (join ", " (List.map ident vs))

let pp_options fmt = function
  | [] -> ()
  | xs -> fprintf fmt "[%a]" (pp_list ~sep:", " pp_option) xs

let pp_newarg fmt = function
  | None -> ()
  | Some [] -> pp_string fmt "[]"
  | Some xs -> fprintf fmt "[%s]" (join ", " (List.map ident xs))

let pp_ident_list fmt xs =
  pp_list ~sep:", " (fun fmt x -> pp_string fmt (ident x)) fmt xs

let pp_typed_ident fmt (x, ty) =
  fprintf fmt "%s:%s" (ident x) (ident ty)

let pp_typed_ident_list fmt xs =
  pp_list ~sep:", " pp_typed_ident fmt xs

let pp_mayfail_typed_ident fmt (x, ty, may_fail) =
  fprintf fmt "%s:%s%s" (ident x) (ident ty) (if may_fail then " or fail" else "")

let pp_mayfail_typed_ident_list fmt xs =
  pp_list ~sep:", " pp_mayfail_typed_ident fmt xs

let pp_forall fmt xs =
  match xs with
  | [] -> ()
  | _ -> fprintf fmt "forall %a; " pp_typed_ident_list xs

let pp_forall_mayfail fmt xs =
  match xs with
  | [] -> ()
  | _ -> fprintf fmt "forall %a; " pp_mayfail_typed_ident_list xs

let pp_env fmt xs =
  match xs with
  | [] -> ()
  | _ -> fprintf fmt "%a; " pp_typed_ident_list xs

let pp_env_mayfail fmt xs =
  match xs with
  | [] -> ()
  | _ -> fprintf fmt "%a; " pp_mayfail_typed_ident_list xs

let always_with_parens = ref false

let with_always_with_parens value f =
  let saved = !always_with_parens in
  always_with_parens := value;
  Fun.protect
    ~finally:(fun () -> always_with_parens := saved)
    f

let pp_paren_if need pp fmt x =
  if need || !always_with_parens then
    fprintf fmt "(%a)" pp x
  else
    pp fmt x

let prec_lowest = 0

let prec_open_branch = 10

let prec_closed_branch = 20

let prec_bar = 30 (* | *)

let prec_semi = 100

let prec_implies = 150

let prec_or = 200 (* || *)

let prec_and = 300

let prec_cmp = 400

let prec_add = 500

let prec_prefix = 600

let prec_app = 700

let prec_atomic = 800

type assoc =
  | Right_assoc
  | Non_assoc

let binary_prec = function
  | "==>" -> Some (prec_implies, Non_assoc)
  | "||" -> Some (prec_or, Right_assoc)
  | "&&" -> Some (prec_and, Right_assoc)
  | "=" | "<>" | "<=" | ">=" | "<" | ">" -> Some (prec_cmp, Non_assoc)
  | _ -> None

let pp_with_comments fmt (comments, f) =
  match comments with
  | [] -> f ()
  | _ ->
      fprintf fmt "@[<v>";
      List.iter (fun c -> fprintf fmt "(* %s *)@ " c) comments;
      f ();
      fprintf fmt "@]"

module Term = struct
  let prec ((t, _, _) : Pitptree.term_e) =
    match t with
    | PFunApp ((name, _), [_; _]) -> begin
        match binary_prec name with
        | Some (prec, _) -> prec
        | None -> prec_app
      end
    | PFunApp (("not", _), [_]) -> prec_prefix
    | PFunApp _ | PProj _ -> prec_app
    | PIdent _ | PFail | PTuple _ -> prec_atomic

  let is_zero ((t, _, _) : Pitptree.term_e) =
    match t with
    | Pitptree.PIdent (name, _) -> name = "0"
    | _ -> false

  let rec decompose_delta ((t, _, _) as te) =
    (* `t + 3` is parsed as `+(+(+ t))`
       `t - 3` is parsed as `"- 3" t`
    *)
    match t with
    | Pitptree.PFunApp (("+", _), [inner]) ->
        let base, delta = decompose_delta inner in
        (base, delta + 1)
    | PFunApp ((name, _), [inner]) when starts_with ~prefix:"- " name ->
        let n = int_of_string (strip_prefix ~prefix:"- " name) in
        let base, delta = decompose_delta inner in
        (base, delta - n)
    | _ -> (te, 0)

  let rec pp_prec ctx_prec fmt te =
    let base, delta = decompose_delta te in
    let my_prec =
      match delta with
      | 0 -> prec te
      | _ -> prec_add
    in
    pp_paren_if (my_prec < ctx_prec) (fun fmt () ->
        match delta with
        | 0 ->
            pp_base fmt base
        | n when is_zero base && n >= 0 ->
            (* 0 + n *)
            Format.pp_print_int fmt n
        | n when n > 0 ->
            fprintf fmt "%a + %d" (pp_prec prec_add) base n
        | n ->
            fprintf fmt "%a - %d" (pp_prec prec_add) base (-n))
      fmt ()

  and pp_base fmt (((t, _, comment) as te) : Pitptree.term_e) =
    let f () =
      match t with
      | Pitptree.PIdent id -> pp_string fmt (ident id)
      | PFail -> pp_string fmt "fail"
      | PFunApp ((("=" | "<>" | "||" | "&&" as name), _), [a; b]) ->
          let my_prec = prec te in
          let left_prec, right_prec =
            match binary_prec name with
            | Some (_, Right_assoc) -> (my_prec + 1, my_prec)
            | Some (_, Non_assoc) -> (my_prec + 1, my_prec + 1)
            | None -> (my_prec, my_prec + 1)
          in
          fprintf fmt "%a %s %a"
            (pp_prec left_prec) a
            name
            (pp_prec right_prec) b
      | PFunApp (("not", _), [a]) ->
          fprintf fmt "not(%a)" pp a
      | PFunApp (("choice", _), [a; b]) ->
          fprintf fmt "choice[%a, %a]" pp a pp b
      | PFunApp (f, args) ->
          fprintf fmt "%s(%a)" (ident f) (pp_list ~sep:", " pp) args
      | PProj (f, t1) -> fprintf fmt "%s(%a)" (ident f) pp t1
      | PTuple ts -> fprintf fmt "(%a)" (pp_list ~sep:", " pp) ts
    in
    pp_with_comments fmt (comment, f)

  and pp fmt te = pp_prec prec_lowest fmt te
end

module Gterm = struct
  let is_zero ((t, _, _) : Pitptree.gterm_e) =
    match t with
    | Pitptree.PGIdent (name, _) -> name = "0"
    | _ -> false

  let pp_opt_at fmt = function
    | None -> ()
    | Some id -> fprintf fmt "@%s" (ident id)

  let rec decompose_delta ((t, _, _) as te) =
    (* `t + 3` is parsed as `+(+(+ t))` *)
    match t with
    | Pitptree.PGFunApp (("+", _), [inner], None) ->
        let base, delta = decompose_delta inner in
        (base, delta + 1)
    | _ -> (te, 0)

  let prec ((t, _, _) : Pitptree.gterm_e) =
    match t with
    | PGIdent _ | PGTuple _ -> prec_atomic
    | PGFunApp ((name, _), [_; _], None) -> begin
        match binary_prec name with
        | Some (prec, _) -> prec
        | None -> prec_app
      end
    | PGFunApp (("not", _), [_], None) -> prec_prefix
    | PGFunApp (_, _, None) -> prec_app
    | PGFunApp (_, _, _) -> prec_app
    | PGPhase _ -> prec_app
    | PGName (_, _) -> prec_app
    | PGLet (_, _, _) -> prec_closed_branch

  let rec pp_prec ctx_prec fmt ge =
    (* base + delta *)
    let base, delta = decompose_delta ge in
    let my_prec =
      match delta with
      | 0 -> prec ge
      | _ -> prec_add
    in
    pp_paren_if (my_prec < ctx_prec) (fun fmt () ->
        match delta with
        | 0 -> pp_base fmt base
        | n when is_zero base && n >= 0 -> Format.pp_print_int fmt n
        | n when n > 0 -> fprintf fmt "%a + %d" (pp_prec prec_add) base n
        | n -> fprintf fmt "%a - %d" (pp_prec prec_add) base (-n))
      fmt ()

  and pp_base fmt (((t, _, comment) as ge): Pitptree.gterm_e) =
    let f () =
      match t with
      | PGIdent id -> pp_string fmt (ident id)
      | PGFunApp ((("=" | "<>" | "||" | "&&" | "<=" | ">=" | "<" | ">" | "==>" as name), _), [a; b], None) ->
          let my_prec = prec ge in
          let left_prec, right_prec =
            match binary_prec name with
            | Some (_, Right_assoc) -> (my_prec + 1, my_prec)
            | Some (_, Non_assoc) -> (my_prec + 1, my_prec + 1)
            | None -> (my_prec, my_prec + 1)
          in
          fprintf fmt "%a %s %a"
            (pp_prec left_prec) a
            name
            (pp_prec right_prec) b
      | PGFunApp (("not", _), [a], None) ->
          fprintf fmt "not(%a)" pp a
      | PGFunApp (("choice", _), [a; b], None) ->
          fprintf fmt "choice[%a, %a]" pp a pp b
      | PGFunApp ((("event" | "inj-event" as name), _), args, at) ->
          fprintf fmt "%s(%a)%a" name (pp_list ~sep:", " pp) args pp_opt_at at
      | PGFunApp (("table", _), [arg], at) ->
          fprintf fmt "table(%a)%a" pp arg pp_opt_at at
      | PGFunApp (f, args, at) ->
          fprintf fmt "%s(%a)%a" (ident f) (pp_list ~sep:", " pp) args pp_opt_at at
      | PGPhase (f, args, phase, at) ->
          fprintf fmt "%s(%a) phase %d%a"
            (ident f)
            (pp_list ~sep:", " pp) args
            phase
            pp_opt_at at
      | PGTuple ts -> fprintf fmt "(%a)" (pp_list ~sep:", " pp) ts
      | PGName (id, bindings) ->
          fprintf fmt "new %s%a"
            (ident id)
            (fun fmt xs ->
               match xs with
               | [] -> ()
               | _ -> fprintf fmt "[%a]" (pp_list ~sep:";@ " pp_gbinding) xs)
            bindings
      | PGLet (id, t1, t2) ->
          fprintf fmt "@[@[<2>let %s =@ %a@]@ in@ %a@]" (ident id) pp t1 pp t2
    in
    pp_with_comments fmt (comment, f)

  and pp fmt ge = pp_prec prec_lowest fmt ge

  and pp_gbinding fmt (id, t) = fprintf fmt "%s = %a" (ident id) pp t
end

module Gformat = struct
  let is_zero ((t, _, _) : Pitptree.gformat_e) =
    match t with
    | Pitptree.PFGIdent (name, _) -> name = "0"
    | _ -> false

  let rec decompose_delta ((t, _, _) as te) =
    match t with
    | Pitptree.PFGFunApp (("+", _), [inner]) ->
        let base, delta = decompose_delta inner in
        (base, delta + 1)
    | _ -> (Some te, 0)

  let rec pp fmt ge =
    (* base + delta *)
    let base, delta = decompose_delta ge in
    match base, delta with
    | None, _ -> assert false
    | Some base, 0 -> pp_base fmt base
    | Some base, n when is_zero base && n >= 0 -> Format.pp_print_int fmt n
    | Some base, n -> fprintf fmt "(%a) + %d" pp_base base n

  and pp_base fmt ((t, _, comment) : Pitptree.gformat_e) =
    let f () =
      match t with
      | PFGIdent id -> pp_string fmt (ident id)
      | PFGFunApp (("choice", _), [a; b]) ->
          fprintf fmt "choice[%a, %a]" pp a pp b
      | PFGFunApp (f, args) -> fprintf fmt "%s(%a)" (ident f) (pp_list ~sep:", " pp) args
      | PFGTuple ts -> fprintf fmt "(%a)" (pp_list ~sep:", " pp) ts
      | PFGName (id, bindings) ->
          fprintf fmt "new %s%a"
            (ident id)
            (fun fmt xs ->
               match xs with
               | [] -> ()
               | _ -> fprintf fmt "[%a]" (pp_list ~sep:";@ " pp_binding) xs)
            bindings
      | PFGAny id -> fprintf fmt "*%s" (ident id)
      | PFGLet (id, t1, t2) ->
          fprintf fmt "@[@[<2>let %s =@ %a@]@ in@ %a@]" (ident id) pp t1 pp t2
    in
    pp_with_comments fmt (comment, f)

  and pp_binding fmt (id, t) = fprintf fmt "%s = %a" (ident id) pp t
end

module Pterm = struct
  let is_zero ((t, _, _) : Pitptree.pterm_e) =
    match t with
    | Pitptree.PPIdent (name, _) -> name = "0"
    | _ -> false

  let pp_basic_pattern fmt = function
    | PPatVar (id, None) -> pp_string fmt (ident id)
    | PPatVar (id, Some ty) -> fprintf fmt "%s:%s" (ident id) (ident ty)
    | PPatAny (_, None) -> pp_string fmt "_"
    | PPatAny (_, Some ty) -> fprintf fmt "_:%s" (ident ty)
    | _ -> assert false

  let pterm_prec ((t, _, _) : Pitptree.pterm_e) =
    match t with
    | PPRestr _ | PPEvent _ | PPInsert _ -> prec_semi (* They contain `;` *)
    | PPTest (_, _, None) -> prec_open_branch
    | PPTest _ -> prec_closed_branch
    | PPLet (_, _, _, None) -> prec_open_branch
    | PPLet _ -> prec_closed_branch
    | PPLetFilter (_, _, _, None) -> prec_open_branch
    | PPLetFilter _ -> prec_closed_branch
    | PPGet (_, _, _, _, None, _) -> prec_open_branch
    | PPGet _ -> prec_closed_branch
    | PPFunApp ((name, _), [_; _]) -> begin
        match binary_prec name with
        | Some (prec, _) -> prec
        | None -> prec_app
      end
    | PPFunApp (("not", _), [_]) -> prec_prefix
    | PPFunApp _ -> prec_app
    | PPIdent _ | PPTuple _ -> prec_atomic

  let rec decompose_delta ((t, _, _) as te) =
    match t with
    | Pitptree.PPFunApp (("+", _), [inner]) ->
        let base, delta, minus = decompose_delta inner in
        if minus then (base, delta - 1, true) else (base, delta + 1, false)
    | PPFunApp ((name, _), [inner]) when starts_with ~prefix:"- " name ->
        let n = int_of_string (strip_prefix ~prefix:"- " name) in
        (inner, n, true)
    | _ -> (te, 0, false)

  let rec pp_prec ctx_prec fmt te =
    let base, delta, minus = decompose_delta te in
    let my_prec =
      match delta, minus with
      | 0, false -> pterm_prec te
      | _, _ -> prec_add
    in
    pp_paren_if (my_prec < ctx_prec) (fun fmt () ->
        match delta, minus with
        | 0, false -> pp_base fmt base
        | n, false when is_zero base && n >= 0 -> Format.pp_print_int fmt n
        | n, false ->
            fprintf fmt "%a + %d" (pp_prec prec_add) base n
        | n, true ->
            fprintf fmt "%a - %d" (pp_prec prec_add) base n)
      fmt ()

  and pp_base fmt (((t, _, comment) as te) : Pitptree.pterm_e) =
    let f () =
      match t with
      | PPIdent id -> pp_string fmt (ident id)
      | PPFunApp ((("=" | "<>" | "||" | "&&" | "<=" | ">=" | "<" | ">" as name), _), [a; b]) ->
          let my_prec = pterm_prec te in
          let left_prec, right_prec =
            match binary_prec name with
            | Some (_, Right_assoc) -> (my_prec + 1, my_prec)
            | Some (_, Non_assoc) -> (my_prec + 1, my_prec + 1)
            | None -> (my_prec, my_prec + 1)
          in
          fprintf fmt "%a %s %a"
            (pp_prec left_prec) a
            name
            (pp_prec right_prec) b
      | PPFunApp (("not", _), [a]) ->
          fprintf fmt "not(%a)" pp a
      | PPFunApp (("choice", _), [a; b]) ->
          fprintf fmt "choice[%a, %a]" pp a pp b
      | PPFunApp (f, args) ->
          fprintf fmt "%s(%a)" (ident f) (pp_list ~sep:", " pp) args
      | PPTuple ts ->
          fprintf fmt "(%a)" (pp_list ~sep:", " pp) ts
      | PPRestr (id, newarg, ty, t1) ->
          fprintf fmt "@[new %s%a:%s;@ %a@]"
            (ident id)
            pp_newarg newarg
            (ident ty)
            (pp_prec prec_semi) t1
      | PPTest (c, t1, None) ->
          fprintf fmt "@[@[<2>if@ %a@]@ @[<2>then@ %a@]@]"
            (pp_prec prec_closed_branch) c
            (pp_prec prec_open_branch) t1
      | PPTest (c, t1, Some t2) ->
          fprintf fmt "@[@[<2>if %a@]@ @[<2>then@ %a@]@ @[<2>else@ %a@]@]"
            (pp_prec prec_closed_branch) c
            (pp_prec prec_closed_branch) t1
            (pp_prec prec_closed_branch) t2
      | PPLet (pat, t1, t2, None) ->
          fprintf fmt "@[@[<2>let %a =@ %a@]@ in@ %a@]"
            pp_tpattern pat pp t1 (pp_prec prec_open_branch) t2
      | PPLet (pat, t1, t2, Some t3) ->
          fprintf fmt "@[@[<2>let %a =@ %a@]@ in@ %a@ @[<2>else %a@]@]"
            pp_tpattern pat pp t1 (pp_prec prec_closed_branch) t2 (pp_prec prec_closed_branch) t3
      | PPLetFilter (env, t1, t2, None) ->
          fprintf fmt "@[@[<2>let %a suchthat@ %a@]@ in@ %a@]"
            pp_typed_ident_list env
            (pp_prec prec_closed_branch) t1
            (pp_prec prec_open_branch) t2
      | PPLetFilter (env, t1, t2, Some t3) ->
          fprintf fmt "@[@[<2>let %a suchthat@ %a@]@ in@ %a@ @[<2>else@ %a@]@]"
            pp_typed_ident_list env
            (pp_prec prec_closed_branch) t1
            (pp_prec prec_closed_branch) t2
            (pp_prec prec_closed_branch) t3
      | PPEvent (id, args, newarg, t1) ->
          fprintf fmt "@[event %s%a%a;@ %a@]"
            (ident id)
            pp_opt_args args
            pp_newarg newarg
            (pp_prec prec_semi) t1
      | PPInsert (id, args, t1) ->
          fprintf fmt "@[insert %s(%a);@ %a@]"
            (ident id)
            (pp_list ~sep:", " pp) args
            (pp_prec prec_semi) t1
      | PPGet (id, pats, cond, body, None, options) ->
          fprintf fmt "@[@[<2>get %s(%a)%a%a@]@ in@ %a@]"
            (ident id)
            (pp_list ~sep:", " pp_tpattern) pats
            (pp_opt_suchthat prec_closed_branch) cond
            pp_options options
            (pp_prec prec_open_branch) body
      | PPGet (id, pats, cond, body, Some else_t, options) ->
          fprintf fmt "@[@[<2>get %s(%a)%a%a@]@ in@ %a@ @[<2>else %a@]@]"
            (ident id)
            (pp_list ~sep:", " pp_tpattern) pats
            (pp_opt_suchthat prec_closed_branch) cond
            pp_options options
            (pp_prec prec_closed_branch) body
            (pp_prec prec_closed_branch) else_t
    in
    pp_with_comments fmt (comment, f)

  and pp fmt te = pp_prec prec_lowest fmt te

  and pp_opt_args fmt = function
    | [] -> ()
    | args -> fprintf fmt "(%a)" (pp_list ~sep:", " pp) args

  and pp_opt_suchthat ctxt_prec fmt = function
    | None -> ()
    | Some t -> fprintf fmt " suchthat@ %a" (pp_prec ctxt_prec) t

  and pp_tpattern fmt = function
    | PPatVar _ as p -> pp_basic_pattern fmt p
    | PPatAny _ as p -> pp_basic_pattern fmt p
    | PPatTuple ps -> fprintf fmt "(%a)" (pp_list ~sep:", " pp_tpattern) ps
    | PPatFunApp (id, ps) -> fprintf fmt "%s(%a)" (ident id) (pp_list ~sep:", " pp_tpattern) ps
    | PPatChoice (id, [a; b], None) ->
        fprintf fmt "%s[%a, %a]" (ident id) pp_tpattern a pp_tpattern b
    | PPatChoice (id, [a; b], Some ty) ->
        fprintf fmt "%s[%a, %a]:%s" (ident id) pp_tpattern a pp_tpattern b (ident ty)
    | PPatChoice (id, ps, ty) ->
        fprintf fmt "%s(%a)%s"
          (ident id)
          (pp_list ~sep:", " pp_tpattern) ps
          (match ty with None -> "" | Some t -> ":" ^ ident t)
    | PPatEqual t -> fprintf fmt "=%a" pp t
end

module Tprocess = struct
  type branch_scope =
    | Open_scope
    | Closed_scope

  type position_ctx =
    | Top_level
    | Sequence_rhs
    | Parallel_left_operand
    | Parallel_right_operand
    | Then_branch
    | Else_branch

  type ctx = {
    prec : int;
    position : position_ctx;
    scope : branch_scope;
  }

  let pp_syncopt fmt = function
    | None -> ()
    | Some (tag, _) when tag = "" -> pp_string fmt "[sync: no tag prefix]"
    | Some tag -> fprintf fmt "[sync: tag prefix %s]" (ident tag)

  let is_nil_process ((p, _, _) : Pitptree.tprocess_e) =
    match p with
    | PNil -> true
    | _ -> false

  let prec ((p, _, _) : Pitptree.tprocess_e) =
    match p with
    | PNil -> prec_atomic
    | PPar _ -> prec_bar
    | PRepl _ -> prec_prefix
    | PRestr (_, _, _, p1) ->
        if is_nil_process p1 then prec_app else prec_semi
    | PLetDef _ -> prec_app
    | PTest (_, _, p2) when is_nil_process p2 -> prec_open_branch
    | PTest _ -> prec_closed_branch
    | PInput (_, _, p1, _) ->
        if is_nil_process p1 then prec_app else prec_semi
    | POutput (_, _, p1) ->
        if is_nil_process p1 then prec_app else prec_semi
    | PLet (_, _, _, p2) when is_nil_process p2 -> prec_open_branch
    | PLet _ -> prec_closed_branch
    | PLetFilter (_, _, _, p2, _) when is_nil_process p2 -> prec_open_branch
    | PLetFilter _ -> prec_closed_branch
    | PEvent (_, _, _, p1) ->
        if is_nil_process p1 then prec_app else prec_semi
    | PPhase (_, p1) ->
        if is_nil_process p1 then prec_app else prec_semi
    | PBarrier (_, _, p1) ->
        if is_nil_process p1 then prec_app else prec_semi
    | PInsert (_, _, p1) ->
        if is_nil_process p1 then prec_app else prec_semi
    | PGet (_, _, _, p1, p2, _) ->
        match is_nil_process p1, is_nil_process p2 with
        | true, true -> prec_open_branch
        | false, true -> prec_open_branch
        | true, false -> prec_open_branch
        | false, false -> prec_closed_branch


  let dummy_ext = Parsing_helper.dummy_ext
  let tprocess_dummy : Pitptree.tprocess_e = PNil, dummy_ext, []

  let ctx ?(position = Top_level) ?(scope = Open_scope) prec =
    { prec; position; scope }

  let sequence_rhs_ctx { scope; _ } =
    match scope with
    | Open_scope -> ctx ~position:Sequence_rhs ~scope prec_open_branch
    | Closed_scope -> ctx ~position:Sequence_rhs ~scope prec_closed_branch

  let then_open_ctx () =
    ctx ~position:Then_branch ~scope:Open_scope prec_open_branch

  let then_closed_ctx () =
    ctx ~position:Then_branch ~scope:Closed_scope prec_closed_branch

  let in_body_ctx () =
    ctx ~position:Sequence_rhs ~scope:Open_scope prec_open_branch

  let else_ctx () =
    ctx ~position:Else_branch ~scope:Closed_scope prec_closed_branch

  let parallel_left_ctx { scope; _ } =
    ctx ~position:Parallel_left_operand ~scope prec_bar

  let parallel_right_ctx { scope; _ } =
    ctx ~position:Parallel_right_operand ~scope prec_bar

  let decompose_semi (((p, ext, comment) as te) : Pitptree.tprocess_e)
    : Pitptree.tprocess_e * Pitptree.tprocess_e option
    =
    match p with
    | PRestr (id, newarg, ty, p1) when not (is_nil_process p1) ->
        (PRestr (id, newarg, ty, tprocess_dummy), ext, comment), Some p1
    | PInput (ch, pat, p1, options) when not (is_nil_process p1) ->
        (PInput (ch, pat, tprocess_dummy, options), ext, comment), Some p1
    | POutput (ch, msg, p1) when not (is_nil_process p1) ->
        (POutput (ch, msg, tprocess_dummy), ext, comment), Some p1
    | PEvent (id, args, newarg, p1) when not (is_nil_process p1) ->
        (PEvent (id, args, newarg, tprocess_dummy), ext, comment), Some p1
    | PPhase (n, p1) when not (is_nil_process p1) ->
        (PPhase (n, tprocess_dummy), ext, comment), Some p1
    | PBarrier (n, o, p1) when not (is_nil_process p1) ->
        (PBarrier (n, o, tprocess_dummy), ext, comment), Some p1
    | PInsert (id, args, p1) when not (is_nil_process p1) ->
        (PInsert (id, args, tprocess_dummy), ext, comment), Some p1
    | _ -> te, None

  let rec pp_ctx ({ prec = ctx_prec; scope; position } as current_ctx) fmt (te : Pitptree.tprocess_e) =
    let te, te'_opt = decompose_semi te in
    let my_prec =
      match te'_opt with
      | Some _ -> prec_semi
      | None -> prec te
    in
    let need_parens_for_parallel_operand =
      match position, te'_opt, te with
      | Parallel_left_operand, Some _, _ -> true
      | Parallel_left_operand, None, (PPar _, _, _) -> true
      | _ -> false
    in
    let is_closed_if =
      match te with
      | PTest (_, _, p2), _, _ when not (is_nil_process p2) -> true
      | _ -> false
    in
    let is_open_let =
      match te with
      | PLet (_, _, _, p2), _, _ when is_nil_process p2 -> true
      | _ -> false
    in
    let allow_naked_parallel_right =
      position = Parallel_right_operand &&
      (is_closed_if || (is_open_let && scope = Open_scope))
    in
    let need_parens_for_closed_scope =
      match scope with
      | Closed_scope ->
          my_prec = prec_open_branch &&
          not allow_naked_parallel_right
      | Open_scope -> false
    in
    let need_parens_for_precedence =
      my_prec < ctx_prec &&
      not allow_naked_parallel_right
    in
    pp_paren_if
      (need_parens_for_parallel_operand || need_parens_for_closed_scope || need_parens_for_precedence)
      (fun fmt () ->
        match te'_opt with
        | Some te' ->
            fprintf fmt "@[<v>%a;@ %a@]"
              (pp_base current_ctx) te
              (pp_ctx (sequence_rhs_ctx current_ctx)) te'
        | None ->
            pp_base current_ctx fmt te)
      fmt ()

  and pp_prec prec fmt te =
    pp_ctx (ctx prec) fmt te

  and pp_base current_ctx fmt ((p, _, comment) : Pitptree.tprocess_e) =
    let f () =
      match p with
      | PNil ->
          pp_string fmt "0"
      | PPar (p1, p2) ->
          fprintf fmt "@[%a |@ %a@]"
            (pp_ctx (parallel_left_ctx current_ctx)) p1
            (pp_ctx (parallel_right_ctx current_ctx)) p2
      | PRepl p1 ->
          fprintf fmt "!%a" (pp_ctx (ctx prec_prefix)) p1

      | PRestr (id, newarg, ty, p1) ->
          if is_nil_process p1 then
            fprintf fmt "@[new %s%a:%s@]"
              (ident id)
              pp_newarg newarg
              (ident ty)
          else
            fprintf fmt "@[new %s%a:%s;@ %a@]"
              (ident id)
              pp_newarg newarg
              (ident ty)
              (pp_prec prec_semi) p1
      | PInput (ch, pat, p1, options) ->
          if is_nil_process p1 then
            fprintf fmt "@[in(%a, %a)%a@]"
              Pterm.pp ch
              Pterm.pp_tpattern pat
              pp_options options
          else
            fprintf fmt "@[in(%a, %a)%a;@ %a@]"
              Pterm.pp ch
              Pterm.pp_tpattern pat
              pp_options options
              (pp_prec prec_semi) p1
      | POutput (ch, msg, p1) ->
          if is_nil_process p1 then
            fprintf fmt "@[out(%a, %a)@]"
              Pterm.pp ch
              Pterm.pp msg
          else
            fprintf fmt "@[out(%a, %a);@ %a@]"
              Pterm.pp ch
              Pterm.pp msg
              (pp_prec prec_semi) p1
      | PEvent (id, args, newarg, p1) ->
          if is_nil_process p1 then
            fprintf fmt "@[event %s%a%a@]"
              (ident id)
              Pterm.pp_opt_args args
              pp_newarg newarg
          else
            fprintf fmt "@[event %s%a%a;@ %a@]"
              (ident id)
              Pterm.pp_opt_args args
              pp_newarg newarg
              (pp_prec prec_semi) p1
      | PPhase (n, p1) ->
          if is_nil_process p1 then
            fprintf fmt "@[phase %d@]" n
          else
            fprintf fmt "@[phase %d;@ %a@]" n (pp_prec prec_semi) p1
      | PBarrier (n, None, p1) ->
          if is_nil_process p1 then
            fprintf fmt "@[sync %d@]" n
          else
            fprintf fmt "@[sync %d;@ %a@]" n (pp_prec prec_semi) p1
      | PBarrier (n, Some tag, p1) ->
          if is_nil_process p1 then
            fprintf fmt "@[sync %d[%s]@]" n (ident tag)
          else
            fprintf fmt "@[sync %d[%s];@ %a@]" n (ident tag) (pp_prec prec_semi) p1
      | PInsert (id, args, p1) ->
          if is_nil_process p1 then
            fprintf fmt "@[insert %s(%a)@]"
              (ident id)
              (pp_list ~sep:", " Pterm.pp) args
          else
            fprintf fmt "@[insert %s(%a);@ %a@]"
              (ident id)
              (pp_list ~sep:", " Pterm.pp) args
              (pp_prec prec_semi) p1

      | PLetDef (id, args, syncopt) ->
          fprintf fmt "%s%a%a"
            (ident id)
            Pterm.pp_opt_args args
            pp_syncopt syncopt
      | PTest (cond, p1, p2) when is_nil_process p2 ->
          fprintf fmt "@[@[<2>if@ %a@]@ @[<2>then@ %a@]@]"
            Pterm.pp cond
            (pp_ctx (then_open_ctx ())) p1
      | PTest (cond, p1, p2) ->
          fprintf fmt "@[@[<2>if@ %a@]@ @[<2>then@ %a@]@ @[<2>else@ %a@]@]"
            Pterm.pp cond
            (pp_ctx (then_closed_ctx ())) p1
            (pp_ctx (else_ctx ())) p2
      | PLet (pat, t1, p1, p2) when is_nil_process p2 ->
          fprintf fmt "@[@[<2>let %a =@ %a@]@ in@ %a@]"
            Pterm.pp_tpattern pat
            Pterm.pp t1
            (pp_ctx (in_body_ctx ())) p1
      | PLet (pat, t1, p1, p2) ->
          fprintf fmt "@[@[<2>let %a =@ %a@]@ in@ %a@ @[<2>else@ %a@]@]"
            Pterm.pp_tpattern pat
            Pterm.pp t1
            (pp_ctx (then_closed_ctx ())) p1
            (pp_ctx (else_ctx ())) p2
      | PLetFilter (env, t1, p1, p2, options) when is_nil_process p2 ->
          fprintf fmt "@[@[<2>let %a suchthat@ %a%a@ in@ %a@]@]"
            pp_typed_ident_list env
            Pterm.pp t1
            pp_options options
            (pp_ctx (in_body_ctx ())) p1
      | PLetFilter (env, t1, p1, p2, options) ->
          fprintf fmt "@[@[<2>let %a suchthat@ %a%a@]@ in@ %a@ @[<2>else@ %a@]@]"
            pp_typed_ident_list env
            Pterm.pp t1
            pp_options options
            (pp_ctx (then_closed_ctx ())) p1
            (pp_ctx (else_ctx ())) p2
      | PGet (id, pats, cond, p1, p2, options) ->
          match is_nil_process p1, is_nil_process p2 with
          | true, true ->
              fprintf fmt "@[@[<2>get %s(%a)%a%a@]@]"
                (ident id)
                (pp_list ~sep:", " Pterm.pp_tpattern) pats
                (Pterm.pp_opt_suchthat prec_closed_branch) cond
                pp_options options
          | false, true ->
              fprintf fmt "@[@[<2>get %s(%a)%a%a@]@ in@ %a@]"
                (ident id)
                (pp_list ~sep:", " Pterm.pp_tpattern) pats
                (Pterm.pp_opt_suchthat prec_closed_branch) cond
                pp_options options
                (pp_ctx (in_body_ctx ())) p1
          | true, false ->
              fprintf fmt "@[@[<2>get %s(%a)%a%a@]@ @[<2>else@ %a@]@]"
                (ident id)
                (pp_list ~sep:", " Pterm.pp_tpattern) pats
                (Pterm.pp_opt_suchthat prec_closed_branch) cond
                pp_options options
                (pp_ctx (else_ctx ())) p2
          | false, false ->
              fprintf fmt "@[@[<2>get %s(%a)%a%a@]@ in@ %a@ @[<2>else@ %a@]@]"
                (ident id)
                (pp_list ~sep:", " Pterm.pp_tpattern) pats
                (Pterm.pp_opt_suchthat prec_closed_branch) cond
                pp_options options
                (pp_ctx (then_closed_ctx ())) p1
                (pp_ctx (else_ctx ())) p2
    in
    pp_with_comments fmt (comment, f)
end

let rec pp_extended_equation fmt = function
  | EELet (id, t, eq) ->
      fprintf fmt "@[@[<2>let %s =@ %a@]@ in@ %a@]"
        (ident id)
        Term.pp t
        pp_extended_equation eq
  | EETerm t ->
      Term.pp fmt t

let pp_eq_clause fmt (env, eq) =
  fprintf fmt "%a%a"
    pp_forall env
    pp_extended_equation eq

let pp_fundef_clause fmt (env, eq) =
  fprintf fmt "%a%a"
    pp_forall_mayfail env
    pp_extended_equation eq

let pp_tclause fmt = function
  | PClause (a, b) ->
      fprintf fmt "%a -> %a"
        Term.pp a
        Term.pp b
  | PFact t ->
      Term.pp fmt t
  | PEquiv (a, b, true) ->
      fprintf fmt "%a <-> %a"
        Term.pp a
        Term.pp b
  | PEquiv (a, b, false) ->
      fprintf fmt "%a <=> %a"
        Term.pp a
        Term.pp b

let rec pp_nounif_t fmt = function
  | BFLet (id, gf, rest) ->
      fprintf fmt "@[@[<2>let %s =@ %a@]@ in@ %a@]@]"
        (ident id)
        Gformat.pp gf
        pp_nounif_t rest
  | BFNoUnif (id, args, phase) ->
      let id_s = ident id in
      if id_s = "table" || id_s = "event" then
        fprintf fmt "%s(%a)"
          id_s
          (pp_list ~sep:", " Gformat.pp) args
      else if args = [] then
        pp_string fmt id_s
      else
        fprintf fmt "%s(%a)"
          id_s
          (pp_list ~sep:", " Gformat.pp) args;
      if phase >= 0 then
        fprintf fmt " phase %d" phase

let pp_nounif_decl fmt env nounif value options =
  match value with
  | Types.NoUnifNegDefault ->
      fprintf fmt "@[<2>nounif %a@,%a%a.@]"
        pp_env env
        pp_nounif_t nounif
        pp_options options
  | Types.NoUnifPosDefault ->
      fprintf fmt "@[<2>select %a@,%a%a.@]"
        pp_env env
        pp_nounif_t nounif
        pp_options options
  | Types.NoUnifValue n ->
      fprintf fmt "@[<2>select %a@,%a /%d%a.@]"
        pp_env env
        pp_nounif_t nounif
        n
        pp_options
        options

let pp_tquery_e fmt ((q, _, _) : Pitptree.tquery_e) =
  match q with
  | PRealQuery (g, pubvars) ->
      fprintf fmt "%a%a"
        Gterm.pp g
        (fun fmt ids ->
          match ids with
          | [] -> ()
          | _ -> fprintf fmt " public_vars %a" pp_ident_list ids)
        pubvars
  | PQSecret (id, pubvars, options) ->
      fprintf fmt "secret %s%a%a"
        (ident id)
        (fun fmt ids ->
          match ids with
          | [] -> ()
          | _ -> fprintf fmt " public_vars %a" pp_ident_list ids)
        pubvars
        pp_options options
  | PPutBegin (false, ids) ->
      fprintf fmt "putbegin event: %a" pp_ident_list ids
  | PPutBegin (true, ids) ->
      fprintf fmt "putbegin inj-event: %a" pp_ident_list ids

let lemma_kind_keyword = function
  | KAxiom -> "axiom"
  | KLemma -> "lemma"
  | KRestriction -> "restriction"

let pp_tlemma fmt (g, ror, pubvars) =
  Gterm.pp fmt g;
  match ror with
  | None when pubvars = [] -> ()
  | None ->
      fprintf fmt " for { public_vars %a }" pp_ident_list pubvars
  | Some (secret, opt) ->
      fprintf fmt " for { secret %s%a [%s] }"
        (ident secret)
        (fun fmt ids ->
          match ids with
          | [] -> ()
          | _ -> fprintf fmt " public_vars %a" pp_ident_list ids)
        pubvars
        (ident opt)

let pp_noninterf_elt fmt (id, terms_opt) =
  match terms_opt with
  | None ->
      pp_string fmt (ident id)
  | Some ts ->
      fprintf fmt "%s among (%a)"
        (ident id)
        (pp_list ~sep:", " Term.pp) ts

let pp_pval fmt = function
  | Ptree.S id -> pp_string fmt (ident id)
  | I n -> Format.pp_print_int fmt n

let rec pp_decl fmt = function
  | TTypeDecl id -> fprintf fmt "type %s." (ident id)
  | TFunDecl (id, args, res, options) ->
      fprintf fmt "@[<2>fun %s(%a):@ %s%a.@]"
        (ident id)
        pp_ident_list args
        (ident res)
        pp_options options
  | TEventDecl (id, []) ->
      fprintf fmt "event %s." (ident id)
  | TEventDecl (id, args) ->
      fprintf fmt "event %s(%a)."
        (ident id)
        pp_ident_list args
  | TConstDecl (id, ty, options) ->
      fprintf fmt "const %s: %s%a."
        (ident id)
        (ident ty)
        pp_options options
  | TReduc (clauses, options) ->
      fprintf fmt "@[<2>reduc@ @[%a@]%a.@]"
        (pp_list ~sep:";@ " pp_eq_clause) clauses
        pp_options options
  | TReducFail (id, args, res, clauses, options) ->
      fprintf fmt "@[<2>fun %s(%a): %s@ @[<2>reduc %a@]%a.@]"
        (ident id)
        pp_ident_list args
        (ident res)
        (pp_list ~sep:";@ " pp_fundef_clause) clauses
        pp_options options
  | TEquation (clauses, options) ->
      fprintf fmt "@[<2>equation @[%a%a@].@]"
        (pp_list ~sep:";@ " pp_eq_clause) clauses
        pp_options options
  | TPredDecl (id, args, options) ->
      if args = [] then
        fprintf fmt "pred %s%a."
          (ident id)
          pp_options options
      else
        fprintf fmt "pred %s(%a)%a."
          (ident id)
          pp_ident_list args
          pp_options options
  | TTableDecl (id, args) ->
      fprintf fmt "table %s(%a)."
        (ident id)
        pp_ident_list args
  | TSet (id, value) ->
      fprintf fmt "set %s = %a."
        (ident id)
        pp_pval value
  | TPDef (id, args, proc) ->
      if args = [] then
        fprintf fmt "@[<2>let %s =@ %a.@]"
          (ident id)
          (Tprocess.pp_prec prec_lowest) proc
      else
        fprintf fmt "@[<2>let %s(%a) =@ %a.@]"
          (ident id)
          pp_mayfail_typed_ident_list args
          (Tprocess.pp_prec prec_lowest) proc
  | TQuery (env, queries, options) ->
      fprintf fmt "@[<2>query %a@,%a%a.@]"
        pp_env env
        (pp_list ~sep:";@ " pp_tquery_e) queries
        pp_options options
  | TNoninterf (env, xs) ->
      fprintf fmt "@[<2>noninterf %a@,%a.@]"
        pp_env env
        (pp_list ~sep:", " pp_noninterf_elt) xs
  | TWeaksecret id ->
      fprintf fmt "weaksecret %s." (ident id)
  | TNoUnif (env, nounif, value, options) ->
      pp_nounif_decl fmt env nounif value options
  | TNot (env, g) ->
      fprintf fmt "@[<2>not %a@,%a.@]"
        pp_env env
        Gterm.pp g
  | TElimtrue (env, t) ->
      fprintf fmt "@[<2>elimtrue %a@,%a.@]"
        pp_env_mayfail env
        Term.pp t
  | TFree (id, ty, options) ->
      fprintf fmt "free %s: %s%a."
        (ident id)
        (ident ty)
        pp_options options
  | TClauses clauses ->
      fprintf fmt "@[<2>clauses@ @[%a.@]@]"
        (pp_list ~sep:";@ "
           (fun fmt (env, cl) ->
             fprintf fmt "%a%a"
               pp_forall_mayfail env
               pp_tclause cl))
        clauses
  | TDefine (id, args, decls) ->
      fprintf fmt "define %s(%a) {@.%a@.}."
        (ident id)
        pp_ident_list args
        (pp_list ~sep:"@," pp_decl)
        decls
  | TExpand (id, args) ->
      fprintf fmt "expand %s(%a)."
        (ident id)
        pp_ident_list args
  | TLetFun (id, args, term) ->
      if args = [] then
        fprintf fmt "@[<2>letfun %s =@ %a.@]"
          (ident id)
          Pterm.pp term
      else
        fprintf fmt "@[<2>letfun %s(%a) =@ %a.@]"
          (ident id)
          pp_mayfail_typed_ident_list args
          Pterm.pp term
  | TLemma (kind, env, lemmas, options) ->
      fprintf fmt "@[<2>%s %a@,%a%a.@]"
        (lemma_kind_keyword kind)
        pp_env env
        (pp_list ~sep:";@ " pp_tlemma) lemmas
        pp_options options
  | TComment comment ->
      fprintf fmt "(* %s *)" comment

let pp_program fmt (decls, proc, second_proc) =
  let pp_decl_text () =
    match decls with
    | [] -> ()
    | _ -> fprintf fmt "@[<v>%a@]@." (pp_list ~sep:"@," pp_decl) decls
  in
  let pp_body () =
    match second_proc with
    | None ->
        fprintf fmt "@[<2>process@ %a.@]@," (Tprocess.pp_prec prec_lowest) proc
    | Some proc2 ->
        fprintf fmt "@[<2>equivalence@ @[(%a)@]@ @[(%a).@]@]@,"
          (Tprocess.pp_prec prec_lowest) proc
          (Tprocess.pp_prec prec_lowest) proc2
  in
  fprintf fmt "@[<v>";
  pp_decl_text ();
  pp_body ();
  fprintf fmt "@]"

let to_string program =
  Format.asprintf "%a@." pp_program program

let to_string_with_parens always program =
  with_always_with_parens always (fun () -> to_string program)

let reparsed_program text =
  Pv_parser.parse_string ~filename:"<pretty-printed>" text

let reparses_to_same_program program text =
  try
    let reparsed = reparsed_program text in
    Pv_ast_equal.equal_program program reparsed
  with
  | Parsing.Parse_error
  | Parsing_helper.InputError _ ->
      false

let to_string_safe program =
  let rendered = to_string program in
  if reparses_to_same_program program rendered then
    (rendered, Ok ())
  else
    let safe_rendered = to_string_with_parens true program in
    let reparsed_safe =
      try reparsed_program safe_rendered with
      | Parsing.Parse_error
      | Parsing_helper.InputError _ ->
          failwith
            "Pv_pp.to_string_safe: parenthesized output does not parse back"
    in
    if Pv_ast_equal.equal_program program reparsed_safe then
      (safe_rendered, Error ())
    else
      failwith
        "Pv_pp.to_string_safe: parenthesized output parses back to a different program"
