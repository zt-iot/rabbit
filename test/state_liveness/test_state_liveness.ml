open Spthy

let check condition message = if not condition then failwith message

let load path =
  let _, decls = Typer.load (Env.init_env ()) path in
  Sem.compile decls

let seed = load "../../examples/000_simplest.rab"
let pid = match snd (List.hd seed.proc_groups) with
  | Sem.Unbounded p -> p.pid
  | Sem.Bounded (_, ps) -> (List.hd ps).pid

let rho = Ident.local "rho"
let x = Ident.local "x"
let y = Ident.local "y"
let c = Ident.local "c"
let node n = Sem.Index.add Sem.Index.zero n
let state ?(pid=pid) ?(transition=None) n mapping =
  State { pid; index = node n; mapping; transition }
let vars = [rho, Ident rho; x, Ident x; y, Ident y]
let rule ?(pre=[]) ?(label=[]) ?(post=[]) () =
  { id = Ident.local "rule"; role = None; pre; label; post; comment = None }
let event e = Global { name = "Seen"; args = [e]; persist = false }
let mapping = function State s -> s.mapping | _ -> failwith "Expected State"
let slots f = List.map fst (mapping f)
let find_state fs = List.find (function State _ -> true | _ -> false) fs

(* This independent checker verifies the local proof obligation: an erased
   source value does not occur in any retained condition, action or output.
   Together with a consistent projection at every State symbol this gives
   both simulation directions for the generated single-State rules. *)
let rec vars_expr = function
  | Ident id -> Ident.Set.singleton id
  | Tuple es | Apply (_, es) -> vars_exprs es
  | Unit | String _ | Integer _ | Index _ | Transition _ -> Ident.Set.empty
and vars_exprs es = List.fold_left (fun acc e ->
    Ident.Set.union acc (vars_expr e)) Ident.Set.empty es

let vars_fact = function
  | State { mapping; pid; _ } ->
      let vs = vars_exprs (List.map snd mapping) in
      (match snd pid with None -> vs | Some p -> Ident.Set.add (p :> Ident.t) vs)
  | Global { args; _ } -> vars_exprs args
  | Const { param; value; _ } -> vars_exprs (value :: Option.to_list param)
  | Eq (a, b) | Neq (a, b) -> vars_exprs [a; b]
  | _ -> failwith "Extend proof checker for this fixture"

let certify before after =
  List.iter2 (fun old reduced ->
      let nonstates = List.filter (function State _ -> false | _ -> true) in
      check (old.id = reduced.id && old.role = reduced.role &&
             old.comment = reduced.comment && old.label = reduced.label &&
             nonstates old.pre = nonstates reduced.pre &&
             nonstates old.post = nonstates reduced.post)
        "Reduction changed a rule or non-State fact";
      List.iter2 (fun a b -> match a, b with
          | State sa, State sb ->
              check (sa.pid = sb.pid && sa.index = sb.index &&
                     sa.transition = sb.transition) "State identity changed";
              check (List.filter (fun (id, _) -> List.mem_assoc id sb.mapping)
                       sa.mapping = sb.mapping) "State values changed";
              let erased = List.filter (fun (id, _) ->
                  not (List.mem_assoc id sb.mapping)) sa.mapping in
              let retained = List.fold_left (fun acc f ->
                  Ident.Set.union acc (vars_fact f)) Ident.Set.empty
                  (reduced.pre @ reduced.label @ reduced.post) in
              List.iter (function
                  | _, Ident id -> check (not (Ident.Set.mem id retained))
                      "Erased value still constrains the reduced rule"
                  | _ -> failwith "Unexpected State premise pattern") erased
          | _ -> ()) old.pre reduced.pre) before after

let reduce rules =
  let reduced = reduce_state_arguments rules in
  certify rules reduced;
  reduced

let () =
  check (not !Config.state_liveness) "State reduction must be disabled by default";
  let rules = [
    rule ~post:[state 0 [rho, Unit; x, String "a"; y, String "b"]] ();
    rule ~pre:[state 0 vars]
      ~post:[state 1 [rho, Unit; x, Ident y; y, Ident y]] ();
    rule ~pre:[state 1 vars] ~label:[event (Ident x)] ~post:[state 2 vars] ()
  ] in
  let reduced = reduce rules in
  check (slots (find_state (List.nth reduced 0).post) = [y])
    "Initialization must retain only y";
  check (slots (find_state (List.nth reduced 1).pre) = [y])
    "Overwritten x and unused rho must die";
  check (slots (find_state (List.nth reduced 1).post) = [x])
    "Live target x must retain its assigned value";
  check (mapping (find_state (List.nth reduced 2).post) = [])
    "Terminal State should have no value slots";
  let branches = reduce [
    rule ~pre:[state 0 vars] ~label:[event (Ident x)] ();
    rule ~pre:[state 0 vars] ~label:[event (Ident y)] ()
  ] in
  List.iter (fun r -> check (slots (find_state r.pre) = [x; y])
      "Branches must use a common union of live slots") branches;
  let loop = reduce [
    rule ~pre:[state 0 vars]
      ~post:[state 0 [rho, Unit; x, Ident y; y, Ident x]] ();
    rule ~pre:[state 0 vars] ~label:[event (Ident x)] ()
  ] in
  check (slots (find_state (List.hd loop).pre) = [x; y])
    "Loop-carried dependencies require a fixed point";
  let guarded = reduce [rule ~pre:[state 0 vars;
      Global { name = "Guard"; args = [Ident x]; persist = false };
      Const { id = c; param = Some (Ident y); value = Ident c }]
      ~label:[Neq (Ident x, String "bad")] ~post:[state 1 vars] ()] in
  check (slots (find_state (List.hd guarded).pre) = [x; y])
    "Premise-only bindings, inequalities and constant parameters must stay live";
  let dependency = Const { id = c; param = None; value = Ident c } in
  let dead_assignment = reduce [rule ~pre:[state 0 [rho, Ident rho]; dependency]
      ~post:[state 1 [rho, Ident c]] ()] in
  check ((List.hd dead_assignment).pre = [state 0 []; dependency])
    "Dead assignment must preserve its constant dependency";
  let register = reduce [
    rule ~pre:[state 0 vars] ~post:[state 1 [rho, Ident x; x, Ident x; y, Ident y]] ();
    rule ~pre:[state 1 vars] ~label:[event (Ident rho)] ()
  ] in
  check (slots (find_state (List.nth register 0).pre) = [x] &&
         slots (find_state (List.nth register 1).pre) = [rho])
    "Return register must participate in liveness";
  let param = Subst.param_id (Ident.local "param") in
  let pid = fst pid, Some param in
  let protected = reduce [rule
      ~pre:[state ~pid ~transition:(Some Var) 0 [rho, Ident rho]]
      ~post:[state ~pid ~transition:(Some Inc) 1 [rho, Unit]] ()] in
  check ((List.hd protected).pre = [state ~pid ~transition:(Some Var) 0 []] &&
         (List.hd protected).post = [state ~pid ~transition:(Some Inc) 1 []])
    "Parameters and counters must survive empty mappings";
  check (String.length (string_of_fact (state 0 [])) > 0)
    "Zero-argument States must print";
  let rho2 = Ident.local "rho" in
  let renamed_register = reduce [
    rule ~pre:[state 0 vars] ~post:[state 1 [rho, Ident x]] ();
    rule ~pre:[state 1 [rho2, Ident rho2]] ~label:[event (Ident rho2)] ()
  ] in
  check (slots (find_state (List.hd renamed_register).pre) = [x])
    "The register must be matched by slot across edge-local identifiers";
  let shadow = Ident.local "x" in
  let shadowed = reduce [rule ~pre:[state 0 [rho, Ident rho; x, Ident x; shadow, Ident shadow]]
      ~label:[event (Ident shadow)] ()] in
  check (slots (find_state (List.hd shadowed).pre) = [shadow])
    "Same-named variables must be distinguished by identity";
  let rejected rules = match reduce_state_arguments rules with
    | _ -> failwith "Unsafe State schema was accepted"
    | exception Invalid_argument _ -> ()
  in
  rejected [rule ~pre:[state 0 vars] ~post:[state 0 [rho, Unit; y, Ident y; x, Ident x]] ()];
  rejected [rule ~pre:[state 0 [rho, Ident x; x, Ident x]] ()]

(* A separate bounded multiset interpreter compares every rule/action trace,
   including blocked runs. It does not use the liveness transfer function. *)
let describe = function
  | State { pid; index; mapping; transition = None } when snd pid = None ->
      "State/" ^ Sem.Index.to_string index, List.map snd mapping, false
  | Global { name; args; persist } -> "Global/" ^ name, args, persist
  | Const { id; param; value } ->
      "Const/" ^ Ident.to_string id, Option.to_list param @ [value], true
  | _ -> failwith "Unsupported interpreter fixture"

let rec substitute bindings = function
  | Ident id -> List.assoc id bindings
  | Tuple es -> Tuple (List.map (substitute bindings) es)
  | Apply (f, es) -> Apply (f, List.map (substitute bindings) es)
  | e -> e

let rec match_expr bindings pattern value =
  match pattern, value with
  | Ident id, _ ->
      (match List.assoc_opt id bindings with
       | None -> Some ((id, value) :: bindings)
       | Some previous -> if previous = value then Some bindings else None)
  | Tuple ps, Tuple vs -> match_exprs bindings ps vs
  | Apply (f, ps), Apply (g, vs) when f = g -> match_exprs bindings ps vs
  | a, b when a = b -> Some bindings
  | _ -> None
and match_exprs bindings ps vs =
  match ps, vs with
  | [], [] -> Some bindings
  | p :: ps, v :: vs ->
      Option.bind (match_expr bindings p v) (fun bindings -> match_exprs bindings ps vs)
  | _ -> None

let instantiate bindings = function
  | State s -> State { s with mapping = List.map (fun (id, e) ->
        id, substitute bindings e) s.mapping }
  | Global g -> Global { g with args = List.map (substitute bindings) g.args }
  | Const c -> Const { c with param = Option.map (substitute bindings) c.param;
                             value = substitute bindings c.value }
  | _ -> failwith "Unsupported interpreter fixture"

let rec consume bindings premises facts =
  match premises with
  | [] -> [bindings, facts]
  | premise :: premises ->
      let name, patterns, persistent = describe premise in
      let rec candidates prefix = function
        | [] -> []
        | f :: rest ->
            let actual, values, _ = describe f in
            let matches =
              if name <> actual then [] else
                match match_exprs bindings patterns values with
                | None -> []
                | Some bindings -> consume bindings premises
                    (if persistent then facts else List.rev_append prefix rest)
            in
            matches @ candidates (f :: prefix) rest
      in
      candidates [] facts

let traces rules depth =
  let rec walk facts prefix depth =
    prefix :: if depth = 0 then [] else
      List.concat_map (fun r ->
          List.concat_map (fun (bindings, remaining) ->
              let labels = List.map (fun f -> string_of_fact (instantiate bindings f)) r.label in
              let step = Ident.to_string r.id ^ ":" ^ String.concat "," labels in
              let facts = remaining @ List.map (instantiate bindings) r.post in
              walk facts (prefix ^ "|" ^ step) (depth - 1))
            (consume [] r.pre facts)) rules
  in
  List.sort_uniq String.compare (walk [] "" depth)

let () =
  let initial = rule ~post:[state 0 [rho, Unit; x, String "a"; y, String "b"]] () in
  let swap = rule ~pre:[state 0 vars]
      ~post:[state 0 [rho, Unit; x, Ident y; y, Ident x]] () in
  let exit = rule ~pre:[state 0 vars] ~label:[event (Ident x)]
      ~post:[state 1 vars] () in
  let overwrite = rule ~pre:[state 0 vars]
      ~post:[state 1 [rho, Unit; x, Ident y; y, Ident y]] () in
  let finish = rule ~pre:[state 1 vars] ~label:[event (Ident x)] () in
  let blocked = rule ~pre:[state 0 vars;
      Const { id = c; param = None; value = Ident c }]
      ~label:[event (String "must remain blocked")]
      ~post:[state 1 [rho, Ident c; x, Ident x; y, Ident y]] () in
  List.iter (fun rules ->
      check (traces rules 6 = traces (reduce rules) 6)
        "Bounded multiset rule/action traces changed")
    [[initial; overwrite; finish]; [initial; swap; exit];
     [initial; exit; rule ~pre:[state 0 vars] ~label:[event (Ident y)] ()];
     [initial; blocked]]

(* Compare complete compiler outputs after removing only State arguments.
   Fresh compiler-generated auxiliary names are compared up to alpha-renaming. *)
let erase_state_args text =
  let re = Str.regexp "State_[A-Za-z_0-9]+(" in
  let out = Buffer.create (String.length text) in
  let rec scan offset =
    match Str.search_forward re text offset with
    | start ->
        let ending = Str.match_end () in
        Buffer.add_substring out text offset (ending - offset);
        let rec close i depth quoted =
          if i >= String.length text then failwith "Unclosed State";
          match text.[i] with
          | '\'' -> close (i + 1) depth (not quoted)
          | '(' when not quoted -> close (i + 1) (depth + 1) quoted
          | ')' when not quoted -> if depth = 1 then i else close (i + 1) (depth - 1) quoted
          | _ -> close (i + 1) depth quoted
        in
        ignore start;
        let ending = close ending 1 false in
        Buffer.add_char out ')';
        scan (ending + 1)
    | exception Not_found ->
        Buffer.add_substring out text offset (String.length text - offset)
  in
  scan 0;
  let names = Hashtbl.create 32 in
  Str.global_substitute (Str.regexp "[A-Za-z_][A-Za-z_0-9]*__[0-9]+")
    (fun text ->
       let name = Str.matched_string text in
       match Hashtbl.find_opt names name with
       | Some replacement -> replacement
       | None ->
           let replacement = "alpha_" ^ string_of_int (Hashtbl.length names) in
           Hashtbl.add names name replacement;
           replacement) (Buffer.contents out)

let () =
  List.iter (fun file ->
      let sem = load ("../../examples/" ^ file ^ ".rab") in
      List.iter (fun compress ->
          let sem = if compress then Sem.optimize sem else sem in
          List.iter (fun tags ->
              Config.tag_transition := tags;
              Config.state_liveness := false;
              let before = Format.asprintf "%a" print (compile_sem sem) in
              Config.state_liveness := true;
              let after = Format.asprintf "%a" print (compile_sem sem) in
              check (erase_state_args before = erase_state_args after)
                ("Non-State compiler output changed: " ^ file)) [false; true])
        [false; true])
    ["000_simplest"; "080_state"; "081_state_param"; "082_state_param_return";
     "090_const"; "110_case"; "130_var"; "150_loop"; "161_structure_param"];
  Config.state_liveness := false;
  Config.tag_transition := true;
  print_endline "State liveness regression tests passed"
