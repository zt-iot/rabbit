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

let is_zero_term ((t, _) : Pitptree.term_e) =
  match t with
  | Pitptree.PIdent (name, _) -> name = "0"
  | _ -> false

let rec decompose_term_delta ((t, _) as te) =
  match t with
  | Pitptree.PFunApp ((name, _), [inner]) when name = "+" ->
      let base, delta = decompose_term_delta inner in
      (base, delta + 1)
  | PFunApp ((name, _), [inner]) when starts_with ~prefix:"- " name ->
      let n = int_of_string (strip_prefix ~prefix:"- " name) in
      let base, delta = decompose_term_delta inner in
      (base, delta - n)
  | _ -> (Some te, 0)

let rec pp_term_e fmt te =
  let base, delta = decompose_term_delta te in
  match base, delta with
  | None, _ -> assert false
  | Some base, 0 -> pp_term_base fmt base
  | Some base, n when is_zero_term base && n >= 0 -> Format.pp_print_int fmt n
  | Some base, n when n > 0 -> fprintf fmt "(%a) + %d" pp_term_base base n
  | Some base, n -> fprintf fmt "(%a) - %d" pp_term_base base (-n)

and pp_term_base fmt ((t, _) : Pitptree.term_e) =
  match t with
  | Pitptree.PIdent id -> pp_string fmt (ident id)
  | PFail -> pp_string fmt "fail"
  | PFunApp ((name, _), [a; b]) when List.mem name [ "="; "<>"; "||"; "&&" ] ->
      fprintf fmt "(%a %s %a)" pp_term_e a name pp_term_e b
  | PFunApp ((name, _), [a]) when name = "not" -> fprintf fmt "not(%a)" pp_term_e a
  | PFunApp ((name, _), [a; b]) when name = "choice" ->
      fprintf fmt "choice[%a, %a]" pp_term_e a pp_term_e b
  | PFunApp (f, args) -> fprintf fmt "%s(%a)" (ident f) (pp_list ~sep:", " pp_term_e) args
  | PProj (f, t1) -> fprintf fmt "%s(%a)" (ident f) pp_term_e t1
  | PTuple ts -> fprintf fmt "(%a)" (pp_list ~sep:", " pp_term_e) ts

let is_zero_gterm ((t, _) : Pitptree.gterm_e) =
  match t with
  | Pitptree.PGIdent (name, _) -> name = "0"
  | _ -> false

let pp_opt_at fmt = function
  | None -> ()
  | Some id -> fprintf fmt "@%s" (ident id)

let rec decompose_gterm_delta ((t, _) as te) =
  match t with
  | Pitptree.PGFunApp ((name, _), [inner], None) when name = "+" ->
      let base, delta = decompose_gterm_delta inner in
      (base, delta + 1)
  | _ -> (Some te, 0)

let rec pp_gterm_e fmt ge =
  let base, delta = decompose_gterm_delta ge in
  match base, delta with
  | None, _ -> assert false
  | Some base, 0 -> pp_gterm_base fmt base
  | Some base, n when is_zero_gterm base && n >= 0 -> Format.pp_print_int fmt n
  | Some base, n when n > 0 -> fprintf fmt "(%a) + %d" pp_gterm_base base n
  | Some base, n -> fprintf fmt "(%a) - %d" pp_gterm_base base (-n)

and pp_gterm_base fmt ((t, _) : Pitptree.gterm_e) =
  match t with
  | PGIdent id -> pp_string fmt (ident id)
  | PGFunApp ((name, _), [a; b], None) when List.mem name ["="; "<>"; "||"; "&&"; "<="; ">="; "<"; ">"; "==>"] ->
      fprintf fmt "(%a %s %a)" pp_gterm_e a name pp_gterm_e b
  | PGFunApp ((name, _), [a], None) when name = "not" -> fprintf fmt "not(%a)" pp_gterm_e a
  | PGFunApp ((name, _), [a; b], None) when name = "choice" ->
      fprintf fmt "choice[%a, %a]" pp_gterm_e a pp_gterm_e b
  | PGFunApp ((name, _), args, at) when name = "event" || name = "inj-event" ->
      fprintf fmt "%s(%a)%a" name (pp_list ~sep:", " pp_gterm_e) args pp_opt_at at
  | PGFunApp ((name, _), [arg], at) when name = "table" ->
      fprintf fmt "table(%a)%a" pp_gterm_e arg pp_opt_at at
  | PGFunApp (f, args, at) ->
      fprintf fmt "%s(%a)%a" (ident f) (pp_list ~sep:", " pp_gterm_e) args pp_opt_at at
  | PGPhase (f, args, phase, at) ->
      fprintf fmt "%s(%a) phase %d%a" (ident f) (pp_list ~sep:", " pp_gterm_e) args phase pp_opt_at at
  | PGTuple ts -> fprintf fmt "(%a)" (pp_list ~sep:", " pp_gterm_e) ts
  | PGName (id, bindings) ->
      fprintf fmt "new %s%a"
        (ident id)
        (fun fmt xs ->
          match xs with
          | [] -> ()
          | _ -> fprintf fmt "[%a]" (pp_list ~sep:";@ " pp_gbinding) xs)
        bindings
  | PGLet (id, t1, t2) ->
      fprintf fmt "@[@[<2>let %s =@ %a@]@ in@ %a@]" (ident id) pp_gterm_e t1 pp_gterm_e t2

and pp_gbinding fmt (id, t) = fprintf fmt "%s = %a" (ident id) pp_gterm_e t

let is_zero_gformat ((t, _) : Pitptree.gformat_e) =
  match t with
  | Pitptree.PFGIdent (name, _) -> name = "0"
  | _ -> false

let rec decompose_gformat_delta ((t, _) as te) =
  match t with
  | Pitptree.PFGFunApp ((name, _), [inner]) when name = "+" ->
      let base, delta = decompose_gformat_delta inner in
      (base, delta + 1)
  | _ -> (Some te, 0)

let rec pp_gformat_e fmt ge =
  let base, delta = decompose_gformat_delta ge in
  match base, delta with
  | None, _ -> assert false
  | Some base, 0 -> pp_gformat_base fmt base
  | Some base, n when is_zero_gformat base && n >= 0 -> Format.pp_print_int fmt n
  | Some base, n -> fprintf fmt "(%a) + %d" pp_gformat_base base n

and pp_gformat_base fmt ((t, _) : Pitptree.gformat_e) =
  match t with
  | PFGIdent id -> pp_string fmt (ident id)
  | PFGFunApp ((name, _), [a; b]) when name = "choice" ->
      fprintf fmt "choice[%a, %a]" pp_gformat_e a pp_gformat_e b
  | PFGFunApp (f, args) -> fprintf fmt "%s(%a)" (ident f) (pp_list ~sep:", " pp_gformat_e) args
  | PFGTuple ts -> fprintf fmt "(%a)" (pp_list ~sep:", " pp_gformat_e) ts
  | PFGName (id, bindings) ->
      fprintf fmt "new %s%a"
        (ident id)
        (fun fmt xs ->
          match xs with
          | [] -> ()
          | _ -> fprintf fmt "[%a]" (pp_list ~sep:";@ " pp_gformat_binding) xs)
        bindings
  | PFGAny id -> fprintf fmt "*%s" (ident id)
  | PFGLet (id, t1, t2) ->
      fprintf fmt "@[@[<2>let %s =@ %a@]@ in@ %a@]" (ident id) pp_gformat_e t1 pp_gformat_e t2

and pp_gformat_binding fmt (id, t) = fprintf fmt "%s = %a" (ident id) pp_gformat_e t

let rec decompose_pterm_delta ((t, _) as te) =
  match t with
  | Pitptree.PPFunApp ((name, _), [inner]) when name = "+" ->
      let base, delta, minus = decompose_pterm_delta inner in
      if minus then (base, delta - 1, true) else (base, delta + 1, false)
  | PPFunApp ((name, _), [inner]) when starts_with ~prefix:"- " name ->
      let n = int_of_string (strip_prefix ~prefix:"- " name) in
      (Some inner, n, true)
  | _ -> (Some te, 0, false)

let is_zero_pterm ((t, _) : Pitptree.pterm_e) =
  match t with
  | Pitptree.PPIdent (name, _) -> name = "0"
  | _ -> false

let pp_basic_pattern fmt = function
  | PPatVar (id, None) -> pp_string fmt (ident id)
  | PPatVar (id, Some ty) -> fprintf fmt "%s:%s" (ident id) (ident ty)
  | PPatAny (_, None) -> pp_string fmt "_"
  | PPatAny (_, Some ty) -> fprintf fmt "_:%s" (ident ty)
  | _ -> assert false

let rec pp_pterm_e fmt te =
  let base, delta, minus = decompose_pterm_delta te in
  match base, delta, minus with
  | None, _, _ -> assert false
  | Some base, 0, false -> pp_pterm_base fmt base
  | Some base, n, false when is_zero_pterm base && n >= 0 -> Format.pp_print_int fmt n
  | Some base, n, false ->
      fprintf fmt "(%a) + %d" pp_pterm_base base n
  | Some base, n, true ->
      fprintf fmt "(%a) - %d" pp_pterm_base base n

and pp_pterm_base fmt ((t, _) : Pitptree.pterm_e) =
  match t with
  | PPIdent id -> pp_string fmt (ident id)
  | PPFunApp ((name, _), [a; b]) when List.mem name ["="; "<>"; "||"; "&&"; "<="; ">="; "<"; ">"] ->
      fprintf fmt "(%a %s %a)" pp_pterm_e a name pp_pterm_e b
  | PPFunApp ((name, _), [a]) when name = "not" ->
      fprintf fmt "not(%a)" pp_pterm_e a
  | PPFunApp ((name, _), [a; b]) when name = "choice" ->
      fprintf fmt "choice[%a, %a]" pp_pterm_e a pp_pterm_e b
  | PPFunApp (f, args) ->
      fprintf fmt "%s(%a)" (ident f) (pp_list ~sep:", " pp_pterm_e) args
  | PPTuple ts ->
      fprintf fmt "(%a)" (pp_list ~sep:", " pp_pterm_e) ts
  | PPRestr (id, newarg, ty, t1) ->
      fprintf fmt "new %s%a:%s; %a"
        (ident id)
        pp_newarg newarg
        (ident ty)
        pp_pterm_e t1
  | PPTest (c, t1, None) ->
      fprintf fmt "@[@[<2>if@ %a@]@ @[<2>then@ %a@]@]" pp_pterm_e c pp_pterm_e t1
  | PPTest (c, t1, Some t2) ->
      fprintf fmt "@[@[<2>if %a@]@ @[<2>then@ %a@]@ @[<2>else@ %a@]@]" pp_pterm_e c pp_pterm_e t1 pp_pterm_e t2
  | PPLet (pat, t1, t2, None) ->
      fprintf fmt "@[@[<2>let %a =@ %a@]@ in@ %a@]" pp_tpattern pat pp_pterm_e t1 pp_pterm_e t2
  | PPLet (pat, t1, t2, Some t3) ->
      fprintf fmt "@[@[<2>let %a =@ %a@]@ in@ %a@ @[<2>else %a@]@]"
        pp_tpattern pat pp_pterm_e t1 pp_pterm_e t2 pp_pterm_e t3
  | PPLetFilter (env, t1, t2, None) ->
      fprintf fmt "@[@[<2>let %a suchthat@ %a@]@ in@ %a@]"
        pp_typed_ident_list env
        pp_pterm_e t1
        pp_pterm_e t2
  | PPLetFilter (env, t1, t2, Some t3) ->
      fprintf fmt "@[@[<2>let %a suchthat@ %a@]@ in@ %a@ @[<2>else@ %a@]@]"
        pp_typed_ident_list env
        pp_pterm_e t1
        pp_pterm_e t2
        pp_pterm_e t3
  | PPEvent (id, args, newarg, t1) ->
      fprintf fmt "event %s%a%a; %a"
        (ident id)
        pp_opt_args args
        pp_newarg newarg
        pp_pterm_e t1
  | PPInsert (id, args, t1) ->
      fprintf fmt "insert %s(%a); %a"
        (ident id)
        (pp_list ~sep:", " pp_pterm_e) args
        pp_pterm_e t1
  | PPGet (id, pats, cond, body, else_t, options) ->
      fprintf fmt "@[@[<2>get %s(%a)%a%a@]@ in@ %a"
        (ident id)
        (pp_list ~sep:", " pp_tpattern) pats
        pp_opt_suchthat cond
        pp_options options
        pp_pterm_e body;
      begin match else_t with
      | None -> ()
      | Some t2 -> fprintf fmt "@ @[<2>else %a@]" pp_pterm_e t2
      end;
      fprintf fmt "@]"

and pp_opt_args fmt = function
  | [] -> ()
  | args -> fprintf fmt "(%a)" (pp_list ~sep:", " pp_pterm_e) args

and pp_opt_suchthat fmt = function
  | None -> ()
  | Some t -> fprintf fmt " suchthat@ %a" pp_pterm_e t

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
  | PPatEqual t -> fprintf fmt "=%a" pp_pterm_e t

let pp_syncopt fmt = function
  | None -> ()
  | Some (tag, _) when tag = "" -> pp_string fmt "[sync: no tag prefix]"
  | Some tag -> fprintf fmt "[sync: tag prefix %s]" (ident tag)

let is_atomic_process ((p, _) : Pitptree.tprocess_e) =
  match p with
  | PNil
  | PLetDef _ -> true
  | _ -> false

let is_nil_process ((p, _) : Pitptree.tprocess_e) =
  match p with
  | PNil -> true
  | _ -> false

let rec pp_tprocess_group fmt p =
  if is_atomic_process p then
    pp_tprocess_e fmt p
  else
    fprintf fmt "(%a)" pp_tprocess_e p

and pp_tprocess_e fmt ((p, _) : Pitptree.tprocess_e) =
  match p with
  | PNil ->
      pp_string fmt "0"
  | PPar (p1, p2) ->
      fprintf fmt "(%a | %a)"
        pp_tprocess_group p1
        pp_tprocess_group p2
  | PRepl p1 ->
      fprintf fmt "! %a"
        pp_tprocess_group p1
  | PRestr (id, newarg, ty, p1) ->
      fprintf fmt "@[new %s%a:%s%a@]"
        (ident id)
        pp_newarg newarg
        (ident ty)
        pp_opttprocess p1
  | PLetDef (id, args, syncopt) ->
      fprintf fmt "%s%a%a"
        (ident id)
        pp_opt_args args
        pp_syncopt syncopt
  | PTest (cond, p1, p2) ->
      fprintf fmt "@[@[<2>if@ %a@]@ @[<2>then@ %a@]"
        pp_pterm_e cond
        pp_tprocess_group p1;
      if not (is_nil_process p2) then
        fprintf fmt "@ @[<2>else@ %a@]" pp_tprocess_group p2;
      fprintf fmt "@]"
  | PInput (ch, pat, p1, options) ->
      fprintf fmt "@[in(%a, %a)%a%a@]"
        pp_pterm_e ch
        pp_tpattern pat
        pp_options options
        pp_opttprocess p1
  | POutput (ch, msg, p1) ->
      fprintf fmt "@[out(%a, %a)%a@]"
        pp_pterm_e ch
        pp_pterm_e msg
        pp_opttprocess p1
  | PLet (pat, t1, p1, p2) ->
      fprintf fmt "@[@[<2>let %a =@ %a@]@ in@ %a"
        pp_tpattern pat
        pp_pterm_e t1
        pp_tprocess_group p1;
      if not (is_nil_process p2) then
        fprintf fmt "@ @[<2>else@ %a@]" pp_tprocess_group p2;
      fprintf fmt "@]"
  | PLetFilter (env, t1, p1, p2, options) ->
      fprintf fmt "@[@[<2>let %a suchthat@ %a%a@ in@ %a@]"
        pp_typed_ident_list env
        pp_pterm_e t1
        pp_options options
        pp_tprocess_group p1;
      if not (is_nil_process p2) then
        fprintf fmt "@ @[<2>else@ %a@]" pp_tprocess_group p2;
      fprintf fmt "@]"
  | PEvent (id, args, newarg, p1) ->
      fprintf fmt "@[event %s%a%a%a@]"
        (ident id)
        pp_opt_args args
        pp_newarg newarg
        pp_opttprocess p1
  | PPhase (n, p1) ->
      fprintf fmt "@[phase %d%a@]"
        n
        pp_opttprocess p1
  | PBarrier (n, None, p1) ->
      fprintf fmt "@[sync %d%a@]"
        n
        pp_opttprocess p1
  | PBarrier (n, Some tag, p1) ->
      fprintf fmt "@[sync %d[%s]%a@]"
        n
        (ident tag)
        pp_opttprocess p1
  | PInsert (id, args, p1) ->
      fprintf fmt "@[insert %s(%a)%a@]"
        (ident id)
        (pp_list ~sep:", " pp_pterm_e) args
        pp_opttprocess p1
  | PGet (id, pats, cond, p1, p2, options) ->
      fprintf fmt "@[@[<2>get %s(%a)%a%a@]"
        (ident id)
        (pp_list ~sep:", " pp_tpattern) pats
        pp_opt_suchthat cond
        pp_options options;
      if not (is_nil_process p1) then
        fprintf fmt "@ in@ %a" pp_tprocess_group p1;
      if not (is_nil_process p2) then
        fprintf fmt "@ @[<2>else@ %a@]" pp_tprocess_group p2;
      fprintf fmt "@]"

and pp_opttprocess fmt p =
  if not (is_nil_process p) then
    fprintf fmt ";@ %a" pp_tprocess_group p

let rec pp_extended_equation fmt = function
  | EELet (id, t, eq) ->
      fprintf fmt "@[@[<2>let %s =@ %a@]@ in@ %a@]"
        (ident id)
        pp_term_e t
        pp_extended_equation eq
  | EETerm t ->
      pp_term_e fmt t

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
        pp_term_e a
        pp_term_e b
  | PFact t ->
      pp_term_e fmt t
  | PEquiv (a, b, true) ->
      fprintf fmt "%a <-> %a"
        pp_term_e a
        pp_term_e b
  | PEquiv (a, b, false) ->
      fprintf fmt "%a <=> %a"
        pp_term_e a
        pp_term_e b

let rec pp_nounif_t fmt = function
  | BFLet (id, gf, rest) ->
      fprintf fmt "@[@[<2>let %s =@ %a@]@ in@ %a@]@]"
        (ident id)
        pp_gformat_e gf
        pp_nounif_t rest
  | BFNoUnif (id, args, phase) ->
      let id_s = ident id in
      if id_s = "table" || id_s = "event" then
        fprintf fmt "%s(%a)"
          id_s
          (pp_list ~sep:", " pp_gformat_e) args
      else if args = [] then
        pp_string fmt id_s
      else
        fprintf fmt "%s(%a)"
          id_s
          (pp_list ~sep:", " pp_gformat_e) args;
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

let pp_tquery_e fmt ((q, _) : Pitptree.tquery_e) =
  match q with
  | PRealQuery (g, pubvars) ->
      fprintf fmt "%a%a"
        pp_gterm_e g
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
  pp_gterm_e fmt g;
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
        (pp_list ~sep:", " pp_term_e) ts

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
          pp_tprocess_e proc
      else
        fprintf fmt "@[<2>let %s(%a) =@ %a.@]"
          (ident id)
          pp_mayfail_typed_ident_list args
          pp_tprocess_e proc
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
        pp_gterm_e g
  | TElimtrue (env, t) ->
      fprintf fmt "@[<2>elimtrue %a@,%a.@]"
        pp_env_mayfail env
        pp_term_e t
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
          pp_pterm_e term
      else
        fprintf fmt "@[<2>letfun %s(%a) =@ %a.@]"
          (ident id)
          pp_mayfail_typed_ident_list args
          pp_pterm_e term
  | TLemma (kind, env, lemmas, options) ->
      fprintf fmt "@[<2>%s %a@,%a%a.@]"
        (lemma_kind_keyword kind)
        pp_env env
        (pp_list ~sep:";@ " pp_tlemma) lemmas
        pp_options options

let pp_program fmt (decls, proc, second_proc) =
  let pp_decl_text () =
    match decls with
    | [] -> ()
    | _ -> fprintf fmt "@[<v>%a@]@." (pp_list ~sep:"@," pp_decl) decls
  in
  let pp_body () =
    match second_proc with
    | None ->
        fprintf fmt "@[<2>process@ %a.@]@," pp_tprocess_e proc
    | Some proc2 ->
        fprintf fmt "@[<2>equivalence@ @[%a@]@ @[%a.@]@]@,"
          pp_tprocess_e proc
          pp_tprocess_e proc2
  in
  fprintf fmt "@[<v>";
  pp_decl_text ();
  pp_body ();
  fprintf fmt "@]"

let to_string program =
  Format.asprintf "%a@." pp_program program
