let failwithf fmt = Printf.ksprintf failwith fmt

open Rabbit_proverif_pv
module Parse = Rabbit_proverif_pv_parse
open Parse
open Pitptree

module Iter = QCheck.Iter

let dummy_ext = Parsing_helper.dummy_ext

let mk_ident s = ((s, dummy_ext) : Pitptree.ident)

let mk_pterm t = (t, dummy_ext, [])

let mk_process p = (p, dummy_ext, [])

let mk_gterm t = (t, dummy_ext, [])

let mk_term t = (t, dummy_ext, [])

let gen_ident =
  let open QCheck.Gen in
  map (fun i -> mk_ident ("x" ^ string_of_int i)) (0 -- 9)

let gen_decl_ident prefix =
  let open QCheck.Gen in
  map (fun i -> mk_ident (prefix ^ string_of_int i)) (0 -- 4)

let gen_type_ident =
  let open QCheck.Gen in
  oneofl [mk_ident "bitstring"; mk_ident "bool"]

let gen_option_list =
  let open QCheck.Gen in
  frequency
    [
      (3, pure []);
      (1, map (fun id -> [ (id, None) ]) (gen_decl_ident "opt"));
      (1, map2 (fun id v -> [ (id, Some [v]) ]) (gen_decl_ident "opt") gen_ident);
    ]

let gen_binary_op =
  let open QCheck.Gen in
  oneofl
    [
      mk_ident "=";
      mk_ident "<>";
      mk_ident "&&";
      mk_ident "||";
      mk_ident "<";
      mk_ident ">";
      mk_ident "<=";
      mk_ident ">=";
    ]

let gen_leaf_term_e =
  let open QCheck.Gen in
  frequency
    [
      (4, map (fun id -> mk_term (PIdent id)) gen_ident);
      (1, pure (mk_term PFail));
    ]

let gen_atomic_term_e =
  let open QCheck.Gen in
  oneof
    [
      gen_leaf_term_e;
      map2 (fun a b -> mk_term (PTuple [a; b])) gen_leaf_term_e gen_leaf_term_e;
      map2 (fun a b -> mk_term (PFunApp (mk_ident "f", [a; b]))) gen_leaf_term_e gen_leaf_term_e;
      map2 (fun a b -> mk_term (PFunApp (mk_ident "choice", [a; b]))) gen_leaf_term_e gen_leaf_term_e;
    ]

let rec gen_term_e size =
  let open QCheck.Gen in
  if size <= 0 then
    gen_leaf_term_e
  else
    frequency
      [
        (2, gen_leaf_term_e);
        (2, gen_atomic_term_e);
        (2, map2 (fun a b -> mk_term (PTuple [a; b])) (gen_term_e (size - 1)) (gen_term_e (size - 1)));
        (2, map2 (fun a b -> mk_term (PFunApp (mk_ident "f", [a; b]))) (gen_term_e (size - 1)) (gen_term_e (size - 1)));
        (1, map2 (fun a b -> mk_term (PFunApp (mk_ident "choice", [a; b]))) (gen_term_e (size - 1)) (gen_term_e (size - 1)));
        (1, map2 (fun a b -> mk_term (PFunApp (mk_ident "=", [a; b]))) gen_atomic_term_e gen_atomic_term_e);
        (1, map (fun a -> mk_term (PFunApp (mk_ident "not", [a]))) gen_atomic_term_e);
      ]

let gen_envdecl =
  let open QCheck.Gen in
  frequency
    [
      (2, pure []);
      (1, map2 (fun id ty -> [ (id, ty) ]) gen_ident gen_type_ident);
    ]

let gen_mayfail_envdecl =
  let open QCheck.Gen in
  frequency
    [
      (2, pure []);
      (1, map3 (fun id ty may_fail -> [ (id, ty, may_fail) ]) gen_ident gen_type_ident bool);
    ]

let gen_extended_equation =
  let open QCheck.Gen in
  frequency
    [
      (2, map (fun t -> EETerm t) (gen_term_e 3));
      (1, map3 (fun id t body -> EELet (id, t, body)) gen_ident (gen_term_e 2) (map (fun t -> EETerm t) (gen_term_e 2)));
    ]

let gen_tclause =
  let open QCheck.Gen in
  frequency
    [
      (2, map2 (fun a b -> PClause (a, b)) (gen_term_e 2) (gen_term_e 2));
      (1, map (fun t -> PFact t) (gen_term_e 2));
      (1, map3 (fun a b strict -> PEquiv (a, b, strict)) (gen_term_e 2) (gen_term_e 2) bool);
    ]

let gen_noninterf_elt =
  let open QCheck.Gen in
  frequency
    [
      (2, map (fun id -> (id, None)) gen_ident);
      (1, map2
            (fun id terms -> (id, Some terms))
            gen_ident
            (list_size (1 -- 2) (gen_term_e 2)));
    ]

let gen_pval =
  let open QCheck.Gen in
  frequency
    [
      (2, map (fun id -> Ptree.S id) gen_ident);
      (1, map (fun n -> Ptree.I n) (0 -- 3));
    ]

let gen_leaf_pterm_e =
  let open QCheck.Gen in
  map (fun id -> mk_pterm (PPIdent id)) gen_ident

let gen_atomic_pterm_e =
  let open QCheck.Gen in
  oneof
    [
      gen_leaf_pterm_e;
      map2 (fun a b -> mk_pterm (PPTuple [a; b])) gen_leaf_pterm_e gen_leaf_pterm_e;
      map3
        (fun a b c -> mk_pterm (PPTuple [a; b; c]))
        gen_leaf_pterm_e
        gen_leaf_pterm_e
        gen_leaf_pterm_e;
      map2 (fun a b -> mk_pterm (PPFunApp (mk_ident "f", [a; b]))) gen_leaf_pterm_e gen_leaf_pterm_e;
      map3
        (fun a b c -> mk_pterm (PPFunApp (mk_ident "g", [a; b; c])))
        gen_leaf_pterm_e
        gen_leaf_pterm_e
        gen_leaf_pterm_e;
      map2 (fun a b -> mk_pterm (PPFunApp (mk_ident "choice", [a; b]))) gen_leaf_pterm_e gen_leaf_pterm_e;
    ]

let gen_comparison_pterm_e =
  let open QCheck.Gen in
  map3
    (fun op a b -> mk_pterm (PPFunApp (op, [a; b])))
    gen_binary_op
    gen_atomic_pterm_e
    gen_atomic_pterm_e

let gen_pattern =
  let open QCheck.Gen in
  let gen_basic_pattern =
    oneof
      [
        map (fun id -> PPatVar (id, None)) gen_ident;
        map2 (fun id ty -> PPatVar (id, Some ty)) gen_ident gen_type_ident;
        pure (PPatAny (dummy_ext, None));
        map (fun ty -> PPatAny (dummy_ext, Some ty)) gen_type_ident;
      ]
  in
  frequency
    [
      (4, gen_basic_pattern);
      (1, map2 (fun a b -> PPatTuple [a; b]) gen_basic_pattern gen_basic_pattern);
      (1, map2 (fun a t -> PPatTuple [a; PPatEqual t]) gen_basic_pattern gen_atomic_pterm_e);
      (1, map2 (fun a b -> PPatFunApp (mk_ident "f", [a; b])) gen_basic_pattern gen_basic_pattern);
      (1, map2 (fun a t -> PPatFunApp (mk_ident "f", [a; PPatEqual t])) gen_basic_pattern gen_atomic_pterm_e);
      (1, map2 (fun a b -> PPatChoice (mk_ident "choice", [a; b], None)) gen_basic_pattern gen_basic_pattern);
      (1, map2 (fun a t -> PPatChoice (mk_ident "choice", [a; PPatEqual t], None)) gen_basic_pattern gen_atomic_pterm_e);
    ]

let gen_typed_env =
  let open QCheck.Gen in
  map2 (fun id ty -> [ (id, ty) ]) gen_ident gen_type_ident

let gen_newarg =
  let open QCheck.Gen in
  frequency
    [
      (3, pure None);
      (1, map (fun id -> Some [id]) gen_ident);
    ]

let gen_phase_num =
  let open QCheck.Gen in
  1 -- 3

let gen_barrier_tag =
  let open QCheck.Gen in
  frequency
    [
      (2, pure None);
      (1, map Option.some gen_ident);
    ]

let gen_small_delta_pterm base_gen =
  let open QCheck.Gen in
  frequency
    [
      (3, base_gen);
      (1, map (fun t -> mk_pterm (PPFunApp (mk_ident "+", [t]))) base_gen);
      (1, map (fun t -> mk_pterm (PPFunApp (mk_ident "- 2", [t]))) base_gen);
    ]

let gen_leaf_gterm_e =
  let open QCheck.Gen in
  map (fun id -> mk_gterm (PGIdent id)) gen_ident

let rec gen_gterm_e size =
  let open QCheck.Gen in
  if size <= 0 then
    gen_leaf_gterm_e
  else
    frequency
      [
        (2, gen_leaf_gterm_e);
        (2, map2 (fun a b -> mk_gterm (PGTuple [a; b])) (gen_gterm_e (size - 1)) (gen_gterm_e (size - 1)));
        (2, map2 (fun a b -> mk_gterm (PGFunApp (mk_ident "f", [a; b], None))) (gen_gterm_e (size - 1)) (gen_gterm_e (size - 1)));
        (1, map2 (fun a b -> mk_gterm (PGFunApp (mk_ident "choice", [a; b], None))) (gen_gterm_e (size - 1)) (gen_gterm_e (size - 1)));
        (1, map2 (fun a b -> mk_gterm (PGFunApp (mk_ident "event", [a; b], None))) (gen_gterm_e (size - 1)) (gen_gterm_e (size - 1)));
        (1, map2 (fun id g -> mk_gterm (PGLet (id, g, mk_gterm (PGIdent id)))) gen_ident (gen_gterm_e (size - 1)));
        (1, map
              (fun ((id, args), phase) -> mk_gterm (PGPhase (id, args, phase, None)))
              (pair
                 (pair (gen_decl_ident "phasef") (QCheck.Gen.list_size (QCheck.Gen.int_bound 2) (gen_gterm_e (size - 1))))
                 gen_phase_num));
      ]

let gen_pubvars =
  QCheck.Gen.list_size (QCheck.Gen.int_bound 2) gen_ident

let gen_tquery_e =
  let open QCheck.Gen in
  map (fun q -> (q, dummy_ext, []))
    (frequency
       [
         (2, map2 (fun g ids -> PRealQuery (g, ids)) (gen_gterm_e 3) gen_pubvars);
         (1, map2 (fun id ids -> PQSecret (id, ids, [])) gen_ident gen_pubvars);
         (1, map (fun ids -> PPutBegin (false, ids)) (list_size (1 -- 3) gen_ident));
         (1, map (fun ids -> PPutBegin (true, ids)) (list_size (1 -- 3) gen_ident));
       ])

let gen_tlemma =
  let open QCheck.Gen in
  map3
    (fun g ror pubvars -> (g, ror, pubvars))
    (gen_gterm_e 3)
    (frequency
       [
         (3, pure None);
         (1, map2 (fun id opt -> Some (id, opt)) gen_ident (gen_decl_ident "opt"));
       ])
    gen_pubvars

let rec gen_open_pterm_e size =
  let open QCheck.Gen in
  if size <= 0 then
    map2 (fun c t1 -> mk_pterm (PPTest (c, t1, None))) gen_leaf_pterm_e gen_leaf_pterm_e
  else
    frequency
      [
        (2, map2 (fun c t1 -> mk_pterm (PPTest (c, t1, None))) (gen_pterm_e (size - 1)) (gen_pterm_e (size - 1)));
        (2, map3
              (fun pat t1 t2 -> mk_pterm (PPLet (pat, t1, t2, None)))
              gen_pattern
              (gen_pterm_e (size - 1))
              (gen_pterm_e (size - 1)));
        (2, map3
              (fun env t1 t2 -> mk_pterm (PPLetFilter (env, t1, t2, None)))
              gen_typed_env
              (gen_pterm_e (size - 1))
              (gen_pterm_e (size - 1)));
        (1, map
              (fun (((id, pat), cond), body) -> mk_pterm (PPGet (id, [pat], cond, body, None, [])))
              (pair
                 (pair
                    (pair gen_ident gen_pattern)
                    (QCheck.Gen.opt (gen_pterm_e (size - 1))))
                 (gen_pterm_e (size - 1))));
      ]

and gen_dangling_pterm_e size =
  let open QCheck.Gen in
  if size <= 0 then
    gen_open_pterm_e 0
  else
    frequency
      [
        (2, map2
              (fun cond else_t -> mk_pterm (PPGet (mk_ident "tbl", [PPatAny (dummy_ext, Some (mk_ident "bitstring"))], Some cond, mk_pterm (PPIdent (mk_ident "x0")), Some else_t, [])))
              (gen_open_pterm_e (size - 1))
              (gen_pterm_e (size - 1)));
        (2, map3
              (fun cond t1 t2 -> mk_pterm (PPTest (cond, t1, Some t2)))
              (gen_open_pterm_e (size - 1))
              (gen_pterm_e (size - 1))
              (gen_pterm_e (size - 1)));
        (1, map3
              (fun pat t1 t2 -> mk_pterm (PPLet (pat, t1, t2, Some (mk_pterm (PPIdent (mk_ident "x1")))))
              )
              gen_pattern
              (gen_open_pterm_e (size - 1))
              (gen_pterm_e (size - 1)));
      ]

and gen_pterm_e size =
  let open QCheck.Gen in
  if size <= 0 then
    gen_leaf_pterm_e
  else
    frequency
      [
        (1, gen_leaf_pterm_e);
        (2, gen_atomic_pterm_e);
        (1, gen_comparison_pterm_e);
        (1, gen_small_delta_pterm gen_atomic_pterm_e);
        (2, map2 (fun a b -> mk_pterm (PPFunApp (mk_ident "f", [a; b]))) (gen_pterm_e (size - 1)) (gen_pterm_e (size - 1)));
        (1, map3
              (fun a b c -> mk_pterm (PPFunApp (mk_ident "g", [a; b; c])))
              (gen_pterm_e (size - 1))
              (gen_pterm_e (size - 1))
              (gen_pterm_e (size - 1)));
        (2, map2 (fun a b -> mk_pterm (PPFunApp (mk_ident "choice", [a; b]))) (gen_pterm_e (size - 1)) (gen_pterm_e (size - 1)));
        (1, map (fun a -> mk_pterm (PPFunApp (mk_ident "not", [a]))) (gen_pterm_e (size - 1)));
        (2, gen_open_pterm_e (size - 1));
        (2, gen_dangling_pterm_e (size - 1));
        (2, map3 (fun c t1 t2 -> mk_pterm (PPTest (c, t1, Some t2))) (gen_pterm_e (size - 1)) (gen_pterm_e (size - 1)) (gen_pterm_e (size - 1)));
        (1, map2 (fun c t1 -> mk_pterm (PPTest (c, t1, None))) (gen_pterm_e (size - 1)) (gen_pterm_e (size - 1)));
        (1, map3 (fun pat t1 t2 -> mk_pterm (PPLet (pat, t1, t2, None))) gen_pattern (gen_pterm_e (size - 1)) (gen_pterm_e (size - 1)));
        (1, map2
              (fun (pat, t1, t2) t3 -> mk_pterm (PPLet (pat, t1, t2, Some t3)))
              (map3
                 (fun pat t1 t2 -> (pat, t1, t2))
                 gen_pattern
                 (gen_pterm_e (size - 1))
                 (gen_pterm_e (size - 1)))
              (gen_pterm_e (size - 1)));
        (1, map
              (fun (((id, newarg), ty), t1) -> mk_pterm (PPRestr (id, newarg, ty, t1)))
              (pair
                 (pair (pair gen_ident gen_newarg) gen_type_ident)
                 (gen_pterm_e (size - 1))));
        (1, map
              (fun (((id, args), newarg), t1) -> mk_pterm (PPEvent (id, args, newarg, t1)))
              (pair
                 (pair
                    (pair gen_ident (QCheck.Gen.list_size (QCheck.Gen.int_bound 2) (gen_pterm_e (size - 1))))
                    gen_newarg)
                 (gen_pterm_e (size - 1))));
        (1, map3
              (fun id args t1 -> mk_pterm (PPInsert (id, args, t1)))
              gen_ident
              (QCheck.Gen.list_size (QCheck.Gen.int_bound 2) (gen_pterm_e (size - 1)))
              (gen_pterm_e (size - 1)));
        (1, map3
              (fun env t1 t2 -> mk_pterm (PPLetFilter (env, t1, t2, None)))
              gen_typed_env
              (gen_pterm_e (size - 1))
              (gen_pterm_e (size - 1)));
        (1, map
              (fun (((env, t1), t2), t3) -> mk_pterm (PPLetFilter (env, t1, t2, Some t3)))
              (pair
                 (pair (pair gen_typed_env (gen_pterm_e (size - 1))) (gen_pterm_e (size - 1)))
                 (gen_pterm_e (size - 1))));
        (1, map
              (fun ((((id, pat), cond), body), else_t) ->
                mk_pterm (PPGet (id, [pat], cond, body, else_t, [])))
              (pair
                 (pair
                    (pair (pair gen_ident gen_pattern) (QCheck.Gen.opt (gen_pterm_e (size - 1))))
                    (gen_pterm_e (size - 1)))
                 (QCheck.Gen.opt (gen_pterm_e (size - 1)))));
      ]

let rec gen_open_tprocess_e size =
  let open QCheck.Gen in
  if size <= 0 then
    map3
      (fun ch pat p -> mk_process (PInput (ch, pat, p, [])))
      gen_leaf_pterm_e
      gen_pattern
      (pure (mk_process PNil))
  else
    frequency
      [
        (2, map3 (fun ch pat p -> mk_process (PInput (ch, pat, p, []))) (gen_pterm_e (size - 1)) gen_pattern (gen_tprocess_e (size - 1)));
        (2, map3 (fun cond p1 p2 -> mk_process (PTest (cond, p1, p2))) (gen_pterm_e (size - 1)) (gen_tprocess_e (size - 1)) (pure (mk_process PNil)));
        (2, map2
              (fun (pat, t, p1) p2 -> mk_process (PLet (pat, t, p1, p2)))
              (map3
                 (fun pat t p1 -> (pat, t, p1))
                 gen_pattern
                 (gen_pterm_e (size - 1))
                 (gen_tprocess_e (size - 1)))
              (pure (mk_process PNil)));
        (1, map2
              (fun (env, t, p1) p2 -> mk_process (PLetFilter (env, t, p1, p2, [])))
              (map3
                 (fun env t p1 -> (env, t, p1))
                 gen_typed_env
                 (gen_pterm_e (size - 1))
                 (gen_tprocess_e (size - 1)))
              (pure (mk_process PNil)));
      ]

and gen_dangling_tprocess_e size =
  let open QCheck.Gen in
  if size <= 0 then
    gen_open_tprocess_e 0
  else
    frequency
      [
        (2, map3
              (fun cond p1 p2 -> mk_process (PTest (cond, p1, p2)))
              (gen_open_pterm_e (size - 1))
              (gen_tprocess_e (size - 1))
              (gen_tprocess_e (size - 1)));
        (2, map2
              (fun (((id, pat), cond), p1) p2 -> mk_process (PGet (id, [pat], Some cond, p1, p2, [])))
              (map
                 (fun (((id, pat), cond), p1) -> (((id, pat), cond), p1))
                 (pair
                    (pair
                       (pair gen_ident gen_pattern)
                       (gen_open_pterm_e (size - 1)))
                    (gen_tprocess_e (size - 1))))
              (gen_tprocess_e (size - 1)));
        (1, map3
              (fun id args p -> mk_process (PEvent (id, args, None, p)))
              gen_ident
              (QCheck.Gen.list_size (QCheck.Gen.int_bound 2) (gen_open_pterm_e (size - 1)))
              (gen_tprocess_e (size - 1)));
      ]

and gen_tprocess_e size =
  let open QCheck.Gen in
  if size <= 0 then
    oneof
      [
        pure (mk_process PNil);
        map (fun id -> mk_process (PLetDef (id, [], None))) gen_ident;
      ]
  else
    frequency
      [
        (1, gen_tprocess_e 0);
        (2, gen_open_tprocess_e (size - 1));
        (2, gen_dangling_tprocess_e (size - 1));
        (2, map2 (fun p1 p2 -> mk_process (PPar (p1, p2))) (gen_tprocess_e (size - 1)) (gen_tprocess_e (size - 1)));
        (1, map (fun p -> mk_process (PRepl p)) (gen_tprocess_e (size - 1)));
        (1, map2 (fun id p -> mk_process (PRestr (id, None, mk_ident "bitstring", p))) gen_ident (gen_tprocess_e (size - 1)));
        (2, map3 (fun ch msg p -> mk_process (POutput (ch, msg, p))) (gen_pterm_e (size - 1)) (gen_pterm_e (size - 1)) (gen_tprocess_e (size - 1)));
        (2, map3 (fun ch pat p -> mk_process (PInput (ch, pat, p, []))) (gen_pterm_e (size - 1)) gen_pattern (gen_tprocess_e (size - 1)));
        (2, map3 (fun c p1 p2 -> mk_process (PTest (c, p1, p2))) (gen_pterm_e (size - 1)) (gen_tprocess_e (size - 1)) (gen_tprocess_e (size - 1)));
        (2, map2
              (fun (pat, t, p1) p2 -> mk_process (PLet (pat, t, p1, p2)))
              (map3
                 (fun pat t p1 -> (pat, t, p1))
                 gen_pattern
                 (gen_pterm_e (size - 1))
                 (gen_tprocess_e (size - 1)))
              (gen_tprocess_e (size - 1)));
        (1, map2
              (fun (env, t, p1) p2 -> mk_process (PLetFilter (env, t, p1, p2, [])))
              (map3
                 (fun env t p1 -> (env, t, p1))
                 gen_typed_env
                 (gen_pterm_e (size - 1))
                 (gen_tprocess_e (size - 1)))
              (gen_tprocess_e (size - 1)));
        (1, map3 (fun id args p -> mk_process (PEvent (id, args, None, p))) gen_ident (QCheck.Gen.list_size (QCheck.Gen.int_bound 2) (gen_pterm_e (size - 1))) (gen_tprocess_e (size - 1)));
        (1, map2 (fun n p -> mk_process (PPhase (n, p))) gen_phase_num (gen_tprocess_e (size - 1)));
        (1, map3 (fun n tag p -> mk_process (PBarrier (n, tag, p))) gen_phase_num gen_barrier_tag (gen_tprocess_e (size - 1)));
        (1, map3
              (fun id args p -> mk_process (PInsert (id, args, p)))
              gen_ident
              (QCheck.Gen.list_size (QCheck.Gen.int_bound 2) (gen_pterm_e (size - 1)))
              (gen_tprocess_e (size - 1)));
        (1, map2
              (fun (((id, pat), cond), p1) p2 -> mk_process (PGet (id, [pat], cond, p1, p2, [])))
              (map
                 (fun (((id, pat), cond), p1) -> (((id, pat), cond), p1))
                 (pair
                    (pair
                       (pair gen_ident gen_pattern)
                       (QCheck.Gen.opt (gen_pterm_e (size - 1))))
                    (gen_tprocess_e (size - 1))))
              (gen_tprocess_e (size - 1)));
      ]

let gen_simple_decl =
  let open QCheck.Gen in
  frequency
    [
      (1, map (fun id -> TTypeDecl id) (gen_decl_ident "ty"));
      (1, map3 (fun id ty opts -> TConstDecl (id, ty, opts)) (gen_decl_ident "c") gen_type_ident gen_option_list);
      (1, map3 (fun id ty opts -> TFree (id, ty, opts)) (gen_decl_ident "free") gen_type_ident gen_option_list);
      (1, map3 (fun id res opts -> TFunDecl (id, [mk_ident "bitstring"], res, opts)) (gen_decl_ident "fun") gen_type_ident gen_option_list);
      (1, map
            (fun (((id, arg), res), opts) -> TFunDecl (id, [arg], res, opts))
            (pair (pair (pair (gen_decl_ident "fun") gen_type_ident) gen_type_ident) gen_option_list));
      (1, map (fun id -> TEventDecl (id, [mk_ident "bitstring"])) (gen_decl_ident "ev"));
      (1, map (fun id -> TEventDecl (id, [])) (gen_decl_ident "ev"));
      (1, map2 (fun id opts -> TPredDecl (id, [mk_ident "bitstring"], opts)) (gen_decl_ident "pred") gen_option_list);
      (1, map2 (fun id opts -> TPredDecl (id, [], opts)) (gen_decl_ident "pred") gen_option_list);
      (1, map (fun id -> TTableDecl (id, [mk_ident "bitstring"])) (gen_decl_ident "tbl"));
      (1, map2 (fun id v -> TSet (id, v)) (gen_decl_ident "set") gen_pval);
      (1, map (fun id -> TWeaksecret id) gen_ident);
      (1, map (fun g -> TNot ([], g)) (gen_gterm_e 3));
      (1, map2 (fun env t -> TElimtrue (env, t)) gen_mayfail_envdecl (gen_term_e 3));
      (2, map2 (fun env cl -> TClauses [ (env, cl) ]) gen_mayfail_envdecl gen_tclause);
      (1, map3 (fun env eq opts -> TEquation ([ (env, eq) ], opts)) gen_envdecl gen_extended_equation gen_option_list);
      (1, map3 (fun env eq opts -> TReduc ([ (env, eq) ], opts)) gen_envdecl gen_extended_equation gen_option_list);
      (1, map
            (fun ((((id, arg), res), env), eq) -> TReducFail (id, [arg], res, [ (env, eq) ], []))
            (pair
               (pair
                  (pair (pair (gen_decl_ident "rf") gen_type_ident) gen_type_ident)
                  gen_mayfail_envdecl)
               gen_extended_equation));
      (1, map2 (fun id t -> TLetFun (id, [], t)) (gen_decl_ident "lf") (gen_pterm_e 3));
      (1, map3 (fun id env p -> TPDef (id, env, p)) (gen_decl_ident "proc") gen_mayfail_envdecl (gen_tprocess_e 2));
      (1, map (fun xs -> TNoninterf ([], xs)) (list_size (1 -- 2) gen_noninterf_elt));
      (1, map2 (fun env xs -> TNoninterf (env, xs)) gen_envdecl (list_size (1 -- 2) gen_noninterf_elt));
      (2, map (fun q -> TQuery ([], [ q ], [])) gen_tquery_e);
      (1, map2 (fun env q -> TQuery (env, [ q ], [])) gen_envdecl gen_tquery_e);
      (1, map2 (fun id args -> TExpand (id, args)) (gen_decl_ident "mac") (list_size (0 -- 2) gen_ident));
      (1, map
            (fun (((kind, env), lemma), opts) -> TLemma (kind, env, [ lemma ], opts))
            (pair
               (pair
                  (pair (oneofl [ KAxiom; KLemma; KRestriction ]) gen_envdecl)
                  gen_tlemma)
               gen_option_list));
    ]

let gen_decls =
  QCheck.Gen.list_size (QCheck.Gen.int_bound 3) gen_simple_decl

let rec shrink_tpattern = function
  | PPatVar _
  | PPatAny _ -> Iter.empty
  | PPatTuple ps ->
      Iter.append
        (Iter.of_list ps)
        (match ps with
         | [] | [ _ ] -> Iter.empty
         | _ -> Iter.of_list [ [ List.hd ps ]; List.tl ps ] |> Iter.map (fun ps' -> PPatTuple ps'))
  | PPatFunApp (id, ps) ->
      Iter.append
        (Iter.of_list ps)
        (match ps with
         | [] | [ _ ] -> Iter.empty
         | _ -> Iter.of_list [ [ List.hd ps ]; List.tl ps ] |> Iter.map (fun ps' -> PPatFunApp (id, ps')))
  | PPatChoice (id, ps, ty) ->
      Iter.append
        (Iter.of_list ps)
        (match ps with
         | [] | [ _ ] -> Iter.empty
         | _ -> Iter.of_list [ [ List.hd ps ]; List.tl ps ] |> Iter.map (fun ps' -> PPatChoice (id, ps', ty)))
  | PPatEqual _ ->
      Iter.return (PPatAny (dummy_ext, None))

and shrink_pterm_e ((t, _, _) : Pitptree.pterm_e) =
  let wrap t' = (t', dummy_ext, []) in
  let iter_to_list iter =
    let acc = ref [] in
    iter (fun x -> acc := x :: !acc);
    List.rev !acc
  in
  let shrink_list_rewrite mk xs =
    let rec aux left = function
      | [] -> []
      | x :: right ->
          let rewritten =
            shrink_pterm_e x
            |> Iter.map (fun x' -> mk (List.rev_append left (x' :: right)))
            |> iter_to_list
          in
          rewritten @ aux (x :: left) right
    in
    Iter.of_list (aux [] xs)
  in
  match t with
  | PPIdent _ -> Iter.empty
  | PPTuple ts ->
      Iter.append
        (Iter.of_list ts)
        (shrink_list_rewrite (fun ts' -> wrap (PPTuple ts')) ts)
  | PPFunApp ((name, _), [a]) when name = "not" || name = "+" || String.length name >= 2 && String.sub name 0 2 = "- " ->
      Iter.append
        (Iter.return a)
        (Iter.map (fun a' -> wrap (PPFunApp (mk_ident name, [a']))) (shrink_pterm_e a))
  | PPFunApp (id, ts) ->
      Iter.append
        (Iter.of_list ts)
        (shrink_list_rewrite (fun ts' -> wrap (PPFunApp (id, ts'))) ts)
  | PPRestr (_, _, _, t1)
  | PPEvent (_, _, _, t1)
  | PPInsert (_, _, t1) ->
      Iter.append
        (Iter.return t1)
        (match t with
         | PPRestr (id, newarg, ty, _) ->
             Iter.map (fun t1' -> wrap (PPRestr (id, newarg, ty, t1'))) (shrink_pterm_e t1)
         | PPEvent (id, args, newarg, _) ->
             let shrink_args = shrink_list_rewrite (fun args' -> wrap (PPEvent (id, args', newarg, t1))) args in
             Iter.append
               shrink_args
               (Iter.map (fun t1' -> wrap (PPEvent (id, args, newarg, t1'))) (shrink_pterm_e t1))
         | PPInsert (id, args, _) ->
             let shrink_args = shrink_list_rewrite (fun args' -> wrap (PPInsert (id, args', t1))) args in
             Iter.append
               shrink_args
               (Iter.map (fun t1' -> wrap (PPInsert (id, args, t1'))) (shrink_pterm_e t1))
         | _ -> Iter.empty)
  | PPTest (c, t1, None) ->
      Iter.append
        (Iter.of_list [ c; t1 ])
        (Iter.append
           (Iter.map (fun c' -> wrap (PPTest (c', t1, None))) (shrink_pterm_e c))
           (Iter.map (fun t1' -> wrap (PPTest (c, t1', None))) (shrink_pterm_e t1)))
  | PPTest (c, t1, Some t2) ->
      Iter.append
        (Iter.of_list [ c; t1; t2 ])
        (Iter.append
           (Iter.map (fun c' -> wrap (PPTest (c', t1, Some t2))) (shrink_pterm_e c))
           (Iter.append
              (Iter.map (fun t1' -> wrap (PPTest (c, t1', Some t2))) (shrink_pterm_e t1))
              (Iter.map (fun t2' -> wrap (PPTest (c, t1, Some t2'))) (shrink_pterm_e t2))))
  | PPLet (_, t1, t2, None) ->
      Iter.append
        (Iter.of_list [ t1; t2 ])
        (match t with
         | PPLet (pat, _, _, None) ->
             Iter.append
               (Iter.map (fun pat' -> wrap (PPLet (pat', t1, t2, None))) (shrink_tpattern pat))
               (Iter.append
                  (Iter.map (fun t1' -> wrap (PPLet (pat, t1', t2, None))) (shrink_pterm_e t1))
                  (Iter.map (fun t2' -> wrap (PPLet (pat, t1, t2', None))) (shrink_pterm_e t2)))
         | _ -> Iter.empty)
  | PPLet (_, t1, t2, Some t3) ->
      Iter.append
        (Iter.of_list [ t1; t2; t3 ])
        (match t with
         | PPLet (pat, _, _, Some _) ->
             Iter.append
               (Iter.map (fun pat' -> wrap (PPLet (pat', t1, t2, Some t3))) (shrink_tpattern pat))
               (Iter.append
                  (Iter.map (fun t1' -> wrap (PPLet (pat, t1', t2, Some t3))) (shrink_pterm_e t1))
                  (Iter.append
                     (Iter.map (fun t2' -> wrap (PPLet (pat, t1, t2', Some t3))) (shrink_pterm_e t2))
                     (Iter.map (fun t3' -> wrap (PPLet (pat, t1, t2, Some t3'))) (shrink_pterm_e t3))))
         | _ -> Iter.empty)
  | PPLetFilter (_, t1, t2, None) ->
      Iter.append
        (Iter.of_list [ t1; t2 ])
        (match t with
         | PPLetFilter (env, _, _, None) ->
             Iter.append
               (Iter.map (fun t1' -> wrap (PPLetFilter (env, t1', t2, None))) (shrink_pterm_e t1))
               (Iter.map (fun t2' -> wrap (PPLetFilter (env, t1, t2', None))) (shrink_pterm_e t2))
         | _ -> Iter.empty)
  | PPLetFilter (_, t1, t2, Some t3) ->
      Iter.append
        (Iter.of_list [ t1; t2; t3 ])
        (match t with
         | PPLetFilter (env, _, _, Some _) ->
             Iter.append
               (Iter.map (fun t1' -> wrap (PPLetFilter (env, t1', t2, Some t3))) (shrink_pterm_e t1))
               (Iter.append
                  (Iter.map (fun t2' -> wrap (PPLetFilter (env, t1, t2', Some t3))) (shrink_pterm_e t2))
                  (Iter.map (fun t3' -> wrap (PPLetFilter (env, t1, t2, Some t3'))) (shrink_pterm_e t3)))
         | _ -> Iter.empty)
  | PPGet (_, _, cond, body, else_t, _) ->
      let basics =
        match cond, else_t with
        | None, None -> [ body ]
        | Some c, None -> [ c; body ]
        | None, Some t2 -> [ body; t2 ]
        | Some c, Some t2 -> [ c; body; t2 ]
      in
      Iter.append
        (Iter.of_list basics)
        (match t with
         | PPGet (id, pats, cond, body, else_t, options) ->
             let shrink_cond =
               match cond with
               | None -> Iter.empty
               | Some c ->
                   Iter.append
                     (Iter.return (wrap (PPGet (id, pats, None, body, else_t, options))))
                     (Iter.map (fun c' -> wrap (PPGet (id, pats, Some c', body, else_t, options))) (shrink_pterm_e c))
             in
             let shrink_body =
               Iter.map (fun body' -> wrap (PPGet (id, pats, cond, body', else_t, options))) (shrink_pterm_e body)
             in
             let shrink_else =
               match else_t with
               | None -> Iter.empty
               | Some t2 ->
                   Iter.append
                     (Iter.return (wrap (PPGet (id, pats, cond, body, None, options))))
                     (Iter.map (fun t2' -> wrap (PPGet (id, pats, cond, body, Some t2', options))) (shrink_pterm_e t2))
             in
             Iter.append shrink_cond (Iter.append shrink_body shrink_else)
         | _ -> Iter.empty)

and shrink_tprocess_e ((p, _, _) : Pitptree.tprocess_e) =
  let wrap p' = (p', dummy_ext, []) in
  match p with
  | PNil
  | PLetDef _ -> Iter.empty
  | PPar (p1, p2) ->
      Iter.append
        (Iter.of_list [p1; p2])
        (Iter.append
           (Iter.map (fun p1' -> wrap (PPar (p1', p2))) (shrink_tprocess_e p1))
           (Iter.map (fun p2' -> wrap (PPar (p1, p2'))) (shrink_tprocess_e p2)))
  | PRepl p1
  | PRestr (_, _, _, p1)
  | PEvent (_, _, _, p1)
  | PPhase (_, p1)
  | PBarrier (_, _, p1)
  | PInsert (_, _, p1) ->
      Iter.append
        (Iter.return p1)
        (match p with
         | PRepl _ ->
             Iter.map (fun p1' -> wrap (PRepl p1')) (shrink_tprocess_e p1)
         | PRestr (id, newarg, ty, _) ->
             Iter.map (fun p1' -> wrap (PRestr (id, newarg, ty, p1'))) (shrink_tprocess_e p1)
         | PEvent (id, args, newarg, _) ->
             let shrink_args =
               let rec aux left = function
                 | [] -> []
                 | x :: right ->
                     let rewritten =
                       shrink_pterm_e x
                       |> Iter.map (fun x' -> wrap (PEvent (id, List.rev_append left (x' :: right), newarg, p1)))
                       |> (fun iter ->
                             let acc = ref [] in
                             iter (fun v -> acc := v :: !acc);
                             List.rev !acc)
                     in
                     rewritten @ aux (x :: left) right
               in
               Iter.of_list (aux [] args)
             in
             Iter.append
               shrink_args
               (Iter.map (fun p1' -> wrap (PEvent (id, args, newarg, p1'))) (shrink_tprocess_e p1))
         | PPhase (n, _) ->
             Iter.map (fun p1' -> wrap (PPhase (n, p1'))) (shrink_tprocess_e p1)
         | PBarrier (n, tag, _) ->
             Iter.map (fun p1' -> wrap (PBarrier (n, tag, p1'))) (shrink_tprocess_e p1)
         | PInsert (id, args, _) ->
             let shrink_args =
               let rec aux left = function
                 | [] -> []
                 | x :: right ->
                     let rewritten =
                       shrink_pterm_e x
                       |> Iter.map (fun x' -> wrap (PInsert (id, List.rev_append left (x' :: right), p1)))
                       |> (fun iter ->
                             let acc = ref [] in
                             iter (fun v -> acc := v :: !acc);
                             List.rev !acc)
                     in
                     rewritten @ aux (x :: left) right
               in
               Iter.of_list (aux [] args)
             in
             Iter.append
               shrink_args
               (Iter.map (fun p1' -> wrap (PInsert (id, args, p1'))) (shrink_tprocess_e p1))
         | _ -> Iter.empty)
  | PTest (c, p1, p2) ->
      Iter.append
        (Iter.of_list [p1; p2])
        (Iter.append
           (Iter.map (fun c' -> wrap (PTest (c', p1, p2))) (shrink_pterm_e c))
           (Iter.append
              (Iter.map (fun p1' -> wrap (PTest (c, p1', p2))) (shrink_tprocess_e p1))
              (Iter.map (fun p2' -> wrap (PTest (c, p1, p2'))) (shrink_tprocess_e p2))))
  | PInput (ch, pat, p1, options) ->
      Iter.append
        (Iter.return p1)
        (Iter.append
           (Iter.map (fun ch' -> wrap (PInput (ch', pat, p1, options))) (shrink_pterm_e ch))
           (Iter.append
              (Iter.map (fun pat' -> wrap (PInput (ch, pat', p1, options))) (shrink_tpattern pat))
              (Iter.map (fun p1' -> wrap (PInput (ch, pat, p1', options))) (shrink_tprocess_e p1))))
  | POutput (ch, msg, p1) ->
      Iter.append
        (Iter.return p1)
        (Iter.append
           (Iter.map (fun ch' -> wrap (POutput (ch', msg, p1))) (shrink_pterm_e ch))
           (Iter.append
              (Iter.map (fun msg' -> wrap (POutput (ch, msg', p1))) (shrink_pterm_e msg))
              (Iter.map (fun p1' -> wrap (POutput (ch, msg, p1'))) (shrink_tprocess_e p1))))
  | PLet (pat, t, p1, p2) ->
      Iter.append
        (Iter.of_list [p1; p2])
        (Iter.append
           (Iter.map (fun t' -> wrap (PLet (pat, t', p1, p2))) (shrink_pterm_e t))
           (Iter.append
              (Iter.map (fun pat' -> wrap (PLet (pat', t, p1, p2))) (shrink_tpattern pat))
              (Iter.append
                 (Iter.map (fun p1' -> wrap (PLet (pat, t, p1', p2))) (shrink_tprocess_e p1))
                 (Iter.map (fun p2' -> wrap (PLet (pat, t, p1, p2'))) (shrink_tprocess_e p2)))))
  | PLetFilter (env, t, p1, p2, options) ->
      Iter.append
        (Iter.of_list [p1; p2])
        (Iter.append
           (Iter.map (fun t' -> wrap (PLetFilter (env, t', p1, p2, options))) (shrink_pterm_e t))
           (Iter.append
              (Iter.map (fun p1' -> wrap (PLetFilter (env, t, p1', p2, options))) (shrink_tprocess_e p1))
              (Iter.map (fun p2' -> wrap (PLetFilter (env, t, p1, p2', options))) (shrink_tprocess_e p2))))
  | PGet (id, pats, cond, p1, p2, options) ->
      let shrink_cond =
        match cond with
        | None -> Iter.empty
        | Some c ->
            Iter.append
              (Iter.return (wrap (PGet (id, pats, None, p1, p2, options))))
              (Iter.map (fun c' -> wrap (PGet (id, pats, Some c', p1, p2, options))) (shrink_pterm_e c))
      in
      let shrink_pats =
        match pats with
        | [] -> Iter.empty
        | pat :: _ ->
            Iter.map (fun pat' -> wrap (PGet (id, [pat'], cond, p1, p2, options))) (shrink_tpattern pat)
      in
      Iter.append
        (Iter.of_list [p1; p2])
        (Iter.append
           shrink_cond
           (Iter.append
              shrink_pats
              (Iter.append
                 (Iter.map (fun p1' -> wrap (PGet (id, pats, cond, p1', p2, options))) (shrink_tprocess_e p1))
                 (Iter.map (fun p2' -> wrap (PGet (id, pats, cond, p1, p2', options))) (shrink_tprocess_e p2)))))

let gen_program =
  let open QCheck.Gen in
  frequency
    [
      (3, map (fun p -> (([] : Pitptree.tdecl list), p, None : Pv_parser.program)) (gen_tprocess_e 5));
      (2, map2
            (fun decls p -> ((decls : Pitptree.tdecl list), p, None : Pv_parser.program))
            gen_decls
            (gen_tprocess_e 5));
      (1, map3
            (fun decls p1 p2 -> ((decls : Pitptree.tdecl list), p1, Some p2 : Pv_parser.program))
            gen_decls
            (gen_tprocess_e 4)
            (gen_tprocess_e 4));
    ]

let shrink_decls decls =
  match decls with
  | [] -> Iter.empty
  | [ _ ] -> Iter.return []
  | _ ->
      let rec drop_each left = function
        | [] -> []
        | x :: right ->
            List.rev_append left right :: drop_each (x :: left) right
      in
      Iter.of_list
        ([] :: List.tl decls :: List.rev (List.tl (List.rev decls)) :: drop_each [] decls)

let shrink_program (decls, p, p2) =
  let shrink_left =
    Iter.map (fun p' -> ((decls, p', p2) : Pv_parser.program)) (shrink_tprocess_e p)
  in
  let shrink_declarations =
    Iter.map (fun decls' -> ((decls', p, p2) : Pv_parser.program)) (shrink_decls decls)
  in
  match p2 with
  | None ->
      Iter.append shrink_declarations shrink_left
  | Some p_right ->
      let shrink_right =
        Iter.map (fun p' -> ((decls, p, Some p') : Pv_parser.program)) (shrink_tprocess_e p_right)
      in
      let drop_to_singletons =
        Iter.of_list
          [
            ((decls, p, None) : Pv_parser.program);
            ((decls, p_right, None) : Pv_parser.program);
            (([], p, None) : Pv_parser.program);
            (([], p_right, None) : Pv_parser.program);
            ((decls, mk_process PNil, Some p_right) : Pv_parser.program);
            ((decls, p, Some (mk_process PNil)) : Pv_parser.program);
          ]
      in
      Iter.append shrink_declarations
        (Iter.append shrink_left (Iter.append shrink_right drop_to_singletons))

let show_program_with_parens program =
  Pv_pp.to_string_with_parens true program

let show_program_without_parens program =
  Pv_pp.to_string_with_parens false program

let roundtrip_parse_result original =
  let unsafe_text = show_program_without_parens original in
  let intended_ast = show_program_with_parens original in
  let reparsed =
    try Some (Pv_parser.parse_string ~filename:"<qcheck>" unsafe_text) with
    | Parsing.Parse_error -> None
  in
  (unsafe_text, intended_ast, reparsed)

let show_roundtrip_counterexample original =
  let unsafe_text, intended_ast, reparsed = roundtrip_parse_result original in
  match reparsed with
  | None ->
      Printf.sprintf
        "Pretty-printed text could not be parsed.\n\
         \n\
         Intended AST (printed safely):\n\
         %s\n\
         \n\
         Unsafe pretty print:\n\
         %s"
        intended_ast
        unsafe_text
  | Some reparsed_ast ->
      let actual_ast = show_program_with_parens reparsed_ast in
      Printf.sprintf
        "Intended AST (printed safely):\n\
         %s\n\
         \n\
         Unsafe pretty print:\n\
         %s\n\
         \n\
         Reparsed AST (printed safely):\n\
         %s"
        intended_ast
        unsafe_text
        actual_ast

let test =
  QCheck.Test.make
    ~count:150
    ~name:"random proverif program roundtrip"
    QCheck.(make ~print:show_roundtrip_counterexample ~shrink:shrink_program gen_program)
    (fun ast1 ->
      let s1, _, parsed = roundtrip_parse_result ast1 in
      match parsed with
      | Some ast2 ->
          let s2 = show_program_without_parens ast2 in
          String.equal s1 s2 && Pv_ast_equal.equal_program ast1 ast2
      | None ->
          false)
