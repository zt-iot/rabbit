open Pitptree

type program = Pv_parser.program

let equal_list eq xs ys =
  List.length xs = List.length ys && List.for_all2 eq xs ys

let equal_option eq x y =
  match x, y with
  | None, None -> true
  | Some x, Some y -> eq x y
  | _ -> false

let equal_ident (s1, _) (s2, _) = String.equal s1 s2

let equal_pval x y =
  match x, y with
  | Ptree.S i1, Ptree.S i2 -> equal_ident i1 i2
  | Ptree.I n1, Ptree.I n2 -> n1 = n2
  | _ -> false

let equal_nounif_value x y =
  match x, y with
  | Types.NoUnifNegDefault, Types.NoUnifNegDefault
  | Types.NoUnifPosDefault, Types.NoUnifPosDefault -> true
  | Types.NoUnifValue n1, Types.NoUnifValue n2 -> n1 = n2
  | _ -> false

let equal_option_decl (id1, vals1) (id2, vals2) =
  equal_ident id1 id2 && equal_option (equal_list equal_ident) vals1 vals2

let rec equal_term_e (t1, _) (t2, _) =
  match t1, t2 with
  | PIdent i1, PIdent i2 -> equal_ident i1 i2
  | PFail, PFail -> true
  | PFunApp (f1, a1), PFunApp (f2, a2) -> equal_ident f1 f2 && equal_list equal_term_e a1 a2
  | PProj (f1, t1), PProj (f2, t2) -> equal_ident f1 f2 && equal_term_e t1 t2
  | PTuple ts1, PTuple ts2 -> equal_list equal_term_e ts1 ts2
  | _ -> false

let rec equal_extended_equation x y =
  match x, y with
  | EELet (i1, t1, e1), EELet (i2, t2, e2) ->
      equal_ident i1 i2 && equal_term_e t1 t2 && equal_extended_equation e1 e2
  | EETerm t1, EETerm t2 -> equal_term_e t1 t2
  | _ -> false

let rec equal_gformat_e (g1, _) (g2, _) =
  match g1, g2 with
  | PFGIdent i1, PFGIdent i2 -> equal_ident i1 i2
  | PFGFunApp (f1, a1), PFGFunApp (f2, a2) -> equal_ident f1 f2 && equal_list equal_gformat_e a1 a2
  | PFGTuple ts1, PFGTuple ts2 -> equal_list equal_gformat_e ts1 ts2
  | PFGName (i1, b1), PFGName (i2, b2) ->
      equal_ident i1 i2 && equal_list (fun (i1, g1) (i2, g2) -> equal_ident i1 i2 && equal_gformat_e g1 g2) b1 b2
  | PFGAny i1, PFGAny i2 -> equal_ident i1 i2
  | PFGLet (i1, g1, h1), PFGLet (i2, g2, h2) ->
      equal_ident i1 i2 && equal_gformat_e g1 g2 && equal_gformat_e h1 h2
  | _ -> false

let rec equal_nounif_t x y =
  match x, y with
  | BFLet (i1, g1, n1), BFLet (i2, g2, n2) ->
      equal_ident i1 i2 && equal_gformat_e g1 g2 && equal_nounif_t n1 n2
  | BFNoUnif (i1, a1, p1), BFNoUnif (i2, a2, p2) ->
      equal_ident i1 i2 && p1 = p2 && equal_list equal_gformat_e a1 a2
  | _ -> false

let rec equal_gterm_e (g1, _) (g2, _) =
  match g1, g2 with
  | PGIdent i1, PGIdent i2 -> equal_ident i1 i2
  | PGFunApp (f1, a1, at1), PGFunApp (f2, a2, at2) ->
      equal_ident f1 f2 && equal_list equal_gterm_e a1 a2 && equal_option equal_ident at1 at2
  | PGPhase (f1, a1, p1, at1), PGPhase (f2, a2, p2, at2) ->
      p1 = p2 && equal_ident f1 f2 && equal_list equal_gterm_e a1 a2 && equal_option equal_ident at1 at2
  | PGTuple ts1, PGTuple ts2 -> equal_list equal_gterm_e ts1 ts2
  | PGName (i1, b1), PGName (i2, b2) ->
      equal_ident i1 i2 && equal_list (fun (i1, g1) (i2, g2) -> equal_ident i1 i2 && equal_gterm_e g1 g2) b1 b2
  | PGLet (i1, g1, h1), PGLet (i2, g2, h2) ->
      equal_ident i1 i2 && equal_gterm_e g1 g2 && equal_gterm_e h1 h2
  | _ -> false

let equal_tquery_e (q1, _) (q2, _) =
  match q1, q2 with
  | PPutBegin (b1, ids1), PPutBegin (b2, ids2) -> b1 = b2 && equal_list equal_ident ids1 ids2
  | PRealQuery (g1, ids1), PRealQuery (g2, ids2) -> equal_gterm_e g1 g2 && equal_list equal_ident ids1 ids2
  | PQSecret (i1, ids1, o1), PQSecret (i2, ids2, o2) ->
      equal_ident i1 i2 && equal_list equal_ident ids1 ids2 && equal_list equal_option_decl o1 o2
  | _ -> false

let equal_lemma_kind x y =
  match x, y with
  | KAxiom, KAxiom
  | KLemma, KLemma
  | KRestriction, KRestriction -> true
  | _ -> false

let equal_tlemma (g1, so1, ids1) (g2, so2, ids2) =
  equal_gterm_e g1 g2 &&
  equal_option (fun (a1, b1) (a2, b2) -> equal_ident a1 a2 && equal_ident b1 b2) so1 so2 &&
  equal_list equal_ident ids1 ids2

let rec equal_pterm_e (p1, _) (p2, _) =
  match p1, p2 with
  | PPIdent i1, PPIdent i2 -> equal_ident i1 i2
  | PPFunApp (f1, a1), PPFunApp (f2, a2) -> equal_ident f1 f2 && equal_list equal_pterm_e a1 a2
  | PPTuple ts1, PPTuple ts2 -> equal_list equal_pterm_e ts1 ts2
  | PPRestr (i1, a1, t1, p1), PPRestr (i2, a2, t2, p2) ->
      equal_ident i1 i2 && equal_option (equal_list equal_ident) a1 a2 && equal_ident t1 t2 && equal_pterm_e p1 p2
  | PPTest (a1, b1, c1), PPTest (a2, b2, c2) ->
      equal_pterm_e a1 a2 && equal_pterm_e b1 b2 && equal_option equal_pterm_e c1 c2
  | PPLet (pat1, a1, b1, c1), PPLet (pat2, a2, b2, c2) ->
      equal_tpattern pat1 pat2 && equal_pterm_e a1 a2 && equal_pterm_e b1 b2 && equal_option equal_pterm_e c1 c2
  | PPLetFilter (env1, a1, b1, c1), PPLetFilter (env2, a2, b2, c2) ->
      equal_list (fun (i1, t1) (i2, t2) -> equal_ident i1 i2 && equal_ident t1 t2) env1 env2 &&
      equal_pterm_e a1 a2 && equal_pterm_e b1 b2 && equal_option equal_pterm_e c1 c2
  | PPEvent (i1, a1, n1, p1), PPEvent (i2, a2, n2, p2) ->
      equal_ident i1 i2 && equal_list equal_pterm_e a1 a2 &&
      equal_option (equal_list equal_ident) n1 n2 && equal_pterm_e p1 p2
  | PPInsert (i1, a1, p1), PPInsert (i2, a2, p2) ->
      equal_ident i1 i2 && equal_list equal_pterm_e a1 a2 && equal_pterm_e p1 p2
  | PPGet (i1, pats1, c1, b1, e1, o1), PPGet (i2, pats2, c2, b2, e2, o2) ->
      equal_ident i1 i2 && equal_list equal_tpattern pats1 pats2 &&
      equal_option equal_pterm_e c1 c2 && equal_pterm_e b1 b2 &&
      equal_option equal_pterm_e e1 e2 && equal_list equal_option_decl o1 o2
  | _ -> false

and equal_tpattern x y =
  match x, y with
  | PPatVar (i1, t1), PPatVar (i2, t2) -> equal_ident i1 i2 && equal_option equal_ident t1 t2
  | PPatAny (_, t1), PPatAny (_, t2) -> equal_option equal_ident t1 t2
  | PPatTuple ps1, PPatTuple ps2 -> equal_list equal_tpattern ps1 ps2
  | PPatFunApp (i1, ps1), PPatFunApp (i2, ps2) -> equal_ident i1 i2 && equal_list equal_tpattern ps1 ps2
  | PPatChoice (i1, ps1, t1), PPatChoice (i2, ps2, t2) ->
      equal_ident i1 i2 && equal_list equal_tpattern ps1 ps2 && equal_option equal_ident t1 t2
  | PPatEqual p1, PPatEqual p2 -> equal_pterm_e p1 p2
  | _ -> false

let rec equal_tprocess_e (p1, _) (p2, _) =
  match p1, p2 with
  | PNil, PNil -> true
  | PPar (a1, b1), PPar (a2, b2) -> equal_tprocess_e a1 a2 && equal_tprocess_e b1 b2
  | PRepl p1, PRepl p2 -> equal_tprocess_e p1 p2
  | PRestr (i1, a1, t1, p1), PRestr (i2, a2, t2, p2) ->
      equal_ident i1 i2 && equal_option (equal_list equal_ident) a1 a2 && equal_ident t1 t2 && equal_tprocess_e p1 p2
  | PLetDef (i1, a1, s1), PLetDef (i2, a2, s2) ->
      equal_ident i1 i2 && equal_list equal_pterm_e a1 a2 &&
      equal_option equal_ident s1 s2
  | PTest (a1, b1, c1), PTest (a2, b2, c2) ->
      equal_pterm_e a1 a2 && equal_tprocess_e b1 b2 && equal_tprocess_e c1 c2
  | PInput (a1, pat1, p1, o1), PInput (a2, pat2, p2, o2) ->
      equal_pterm_e a1 a2 && equal_tpattern pat1 pat2 && equal_tprocess_e p1 p2 && equal_list equal_option_decl o1 o2
  | POutput (a1, b1, p1), POutput (a2, b2, p2) ->
      equal_pterm_e a1 a2 && equal_pterm_e b1 b2 && equal_tprocess_e p1 p2
  | PLet (pat1, a1, b1, c1), PLet (pat2, a2, b2, c2) ->
      equal_tpattern pat1 pat2 && equal_pterm_e a1 a2 && equal_tprocess_e b1 b2 && equal_tprocess_e c1 c2
  | PLetFilter (env1, a1, b1, c1, o1), PLetFilter (env2, a2, b2, c2, o2) ->
      equal_list (fun (i1, t1) (i2, t2) -> equal_ident i1 i2 && equal_ident t1 t2) env1 env2 &&
      equal_pterm_e a1 a2 && equal_tprocess_e b1 b2 && equal_tprocess_e c1 c2 && equal_list equal_option_decl o1 o2
  | PEvent (i1, a1, n1, p1), PEvent (i2, a2, n2, p2) ->
      equal_ident i1 i2 && equal_list equal_pterm_e a1 a2 &&
      equal_option (equal_list equal_ident) n1 n2 && equal_tprocess_e p1 p2
  | PPhase (n1, p1), PPhase (n2, p2) -> n1 = n2 && equal_tprocess_e p1 p2
  | PBarrier (n1, i1, p1), PBarrier (n2, i2, p2) ->
      n1 = n2 && equal_option equal_ident i1 i2 && equal_tprocess_e p1 p2
  | PInsert (i1, a1, p1), PInsert (i2, a2, p2) ->
      equal_ident i1 i2 && equal_list equal_pterm_e a1 a2 && equal_tprocess_e p1 p2
  | PGet (i1, pats1, c1, b1, e1, o1), PGet (i2, pats2, c2, b2, e2, o2) ->
      equal_ident i1 i2 && equal_list equal_tpattern pats1 pats2 &&
      equal_option equal_pterm_e c1 c2 && equal_tprocess_e b1 b2 &&
      equal_tprocess_e e1 e2 && equal_list equal_option_decl o1 o2
  | _ -> false

let equal_tclause x y =
  match x, y with
  | PClause (a1, b1), PClause (a2, b2) -> equal_term_e a1 a2 && equal_term_e b1 b2
  | PFact t1, PFact t2 -> equal_term_e t1 t2
  | PEquiv (a1, b1, c1), PEquiv (a2, b2, c2) -> c1 = c2 && equal_term_e a1 a2 && equal_term_e b1 b2
  | _ -> false

let rec equal_tdecl x y =
  match x, y with
  | TTypeDecl i1, TTypeDecl i2 -> equal_ident i1 i2
  | TFunDecl (i1, a1, r1, o1), TFunDecl (i2, a2, r2, o2) ->
      equal_ident i1 i2 && equal_list equal_ident a1 a2 && equal_ident r1 r2 && equal_list equal_option_decl o1 o2
  | TEventDecl (i1, a1), TEventDecl (i2, a2) ->
      equal_ident i1 i2 && equal_list equal_ident a1 a2
  | TConstDecl (i1, t1, o1), TConstDecl (i2, t2, o2) ->
      equal_ident i1 i2 && equal_ident t1 t2 && equal_list equal_option_decl o1 o2
  | TReduc (xs1, o1), TReduc (xs2, o2)
  | TEquation (xs1, o1), TEquation (xs2, o2) ->
      equal_list (fun (e1, q1) (e2, q2) -> equal_list (fun (i1, t1) (i2, t2) -> equal_ident i1 i2 && equal_ident t1 t2) e1 e2 && equal_extended_equation q1 q2) xs1 xs2
      && equal_list equal_option_decl o1 o2
  | TReducFail (i1, a1, r1, xs1, o1), TReducFail (i2, a2, r2, xs2, o2) ->
      equal_ident i1 i2 && equal_list equal_ident a1 a2 && equal_ident r1 r2 &&
      equal_list
        (fun (e1, q1) (e2, q2) ->
          equal_list (fun (i1, t1, b1) (i2, t2, b2) -> b1 = b2 && equal_ident i1 i2 && equal_ident t1 t2) e1 e2 &&
          equal_extended_equation q1 q2)
        xs1 xs2 &&
      equal_list equal_option_decl o1 o2
  | TPredDecl (i1, a1, o1), TPredDecl (i2, a2, o2) ->
      equal_ident i1 i2 && equal_list equal_ident a1 a2 && equal_list equal_option_decl o1 o2
  | TTableDecl (i1, a1), TTableDecl (i2, a2) ->
      equal_ident i1 i2 && equal_list equal_ident a1 a2
  | TSet (i1, v1), TSet (i2, v2) ->
      equal_ident i1 i2 && equal_pval v1 v2
  | TPDef (i1, a1, p1), TPDef (i2, a2, p2) ->
      equal_ident i1 i2 &&
      equal_list (fun (i1, t1, b1) (i2, t2, b2) -> b1 = b2 && equal_ident i1 i2 && equal_ident t1 t2) a1 a2 &&
      equal_tprocess_e p1 p2
  | TLetFun (i1, a1, p1), TLetFun (i2, a2, p2) ->
      equal_ident i1 i2 &&
      equal_list (fun (i1, t1, b1) (i2, t2, b2) -> b1 = b2 && equal_ident i1 i2 && equal_ident t1 t2) a1 a2 &&
      equal_pterm_e p1 p2
  | TQuery (e1, q1, o1), TQuery (e2, q2, o2) ->
      equal_list (fun (i1, t1) (i2, t2) -> equal_ident i1 i2 && equal_ident t1 t2) e1 e2 &&
      equal_list equal_tquery_e q1 q2 &&
      equal_list equal_option_decl o1 o2
  | TNoninterf (e1, xs1), TNoninterf (e2, xs2) ->
      equal_list (fun (i1, t1) (i2, t2) -> equal_ident i1 i2 && equal_ident t1 t2) e1 e2 &&
      equal_list (fun (i1, ts1) (i2, ts2) -> equal_ident i1 i2 && equal_option (equal_list equal_term_e) ts1 ts2) xs1 xs2
  | TWeaksecret i1, TWeaksecret i2 -> equal_ident i1 i2
  | TNoUnif (e1, n1, v1, o1), TNoUnif (e2, n2, v2, o2) ->
      equal_list (fun (i1, t1) (i2, t2) -> equal_ident i1 i2 && equal_ident t1 t2) e1 e2 &&
      equal_nounif_t n1 n2 &&
      equal_nounif_value v1 v2 &&
      equal_list equal_option_decl o1 o2
  | TNot (e1, g1), TNot (e2, g2) ->
      equal_list (fun (i1, t1) (i2, t2) -> equal_ident i1 i2 && equal_ident t1 t2) e1 e2 &&
      equal_gterm_e g1 g2
  | TElimtrue (e1, t1), TElimtrue (e2, t2) ->
      equal_list (fun (i1, t1, b1) (i2, t2, b2) -> b1 = b2 && equal_ident i1 i2 && equal_ident t1 t2) e1 e2 &&
      equal_term_e t1 t2
  | TFree (i1, t1, o1), TFree (i2, t2, o2) ->
      equal_ident i1 i2 && equal_ident t1 t2 && equal_list equal_option_decl o1 o2
  | TClauses c1, TClauses c2 ->
      equal_list
        (fun (e1, cl1) (e2, cl2) ->
          equal_list (fun (i1, t1, b1) (i2, t2, b2) -> b1 = b2 && equal_ident i1 i2 && equal_ident t1 t2) e1 e2 &&
          equal_tclause cl1 cl2)
        c1 c2
  | TDefine (i1, a1, d1), TDefine (i2, a2, d2) ->
      equal_ident i1 i2 && equal_list equal_ident a1 a2 && equal_list equal_tdecl d1 d2
  | TExpand (i1, a1), TExpand (i2, a2) ->
      equal_ident i1 i2 && equal_list equal_ident a1 a2
  | TLemma (k1, e1, l1, o1), TLemma (k2, e2, l2, o2) ->
      equal_lemma_kind k1 k2 &&
      equal_list (fun (i1, t1) (i2, t2) -> equal_ident i1 i2 && equal_ident t1 t2) e1 e2 &&
      equal_list equal_tlemma l1 l2 &&
      equal_list equal_option_decl o1 o2
  | _ -> false

let equal_program (decls1, p1, p1b) (decls2, p2, p2b) =
  equal_list equal_tdecl decls1 decls2 &&
  equal_tprocess_e p1 p2 &&
  equal_option equal_tprocess_e p1b p2b
