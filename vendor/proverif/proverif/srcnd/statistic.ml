(*************
  Statistic
**************)

let initial_time = (Unix.times ()).Unix.tms_utime

type stat =
  {
    mutable recorded: bool;
    mutable time : float;
    mutable call : int;
    name : string;
  }

let record_time ref_t f =
  ref_t.recorded <- true;
  let t0 = Unix.times () in
  let r = f () in
  let t1 = Unix.times () in
  ref_t.time <- ref_t.time +. t1.Unix.tms_utime -. t0.Unix.tms_utime;
  ref_t.call <- ref_t.call + 1;
  r

let record_one s f =
  let t0 = Unix.times () in
  let r = f () in
  let t1 = Unix.times () in
  Printf.printf "COMPUTATIONTIME %s: %fs\n" s (t1.Unix.tms_utime -. t0.Unix.tms_utime);
  r

let number_of_implies = ref 0
let record_number_of_implies s f =
  let tmp = !number_of_implies in
  number_of_implies := 0;
  let r = f () in
  Printf.printf "NUMBERIMPLIES %s: %d\n" s !number_of_implies;
  number_of_implies := tmp;
  r

let record_discountenous ref_f =
  let t0 = ref (Unix.times ()).Unix.tms_utime in

  let stop () =
    let t1 = (Unix.times ()).Unix.tms_utime in
    ref_f.time <- ref_f.time +. t1 -. !t0
  in

  let continue () =
    t0 := (Unix.times ()).Unix.tms_utime
  in

  stop, continue

(******* The function recorded ******)

let create name =
  { name = name; time = 0.; call = 0; recorded = false }

let time_simplify = create "simplify"
let stop_simp, go_simp = record_discountenous time_simplify

let time_generate_feature_vertex = create "generate_feature_vertex"
let time_generate_subsumption_data = create "generate_subsumption_data"
let time_implies = create "implies"

let time_ClauseSet_add = create "CSet.add"
let time_ClauseSet_deactivate_implied_by = create "CSet.deactivate_implied_by"
let time_ClauseSet_cleanup_deactivated = create "CSet.cleanup_deactivated"
let time_ClauseSet_implies = create "CSet.implies"

let time_ClauseQueue_add = create "CQueue.add"
let time_ClauseQueue_get = create "CQueue.get"
let time_ClauseQueue_deactivate_implied_by = create "CQueue.deactivate_implied_by"
let time_ClauseQueue_implies = create "CQueue.implies"
let time_ClauseQueue_cleanup_deactivated = create "CQueue.cleanup_deactivated"

let time_add_rule = create "add_rule"
let time_redundant_glob = create "redundant_glob"
let time_is_unselectable = create "is_unselectable"
let time_compo = create "compo"
let time_elim_and_tuple = create "elim_and_tuple"
let time_selection_fun = create "selection_fun"

let time_transl_process = create "transl_process"
let time_check_feasible = create "check_feasible"
let time_check_final_feasible = create "check_final_feasible"

let display_statistics () =
  Printf.printf "----------------\n";
  Printf.printf "Total computation time : %fs\n" ((Unix.times ()).Unix.tms_utime -. initial_time);
  Printf.printf "Computation times:\n";
  let f r = if r.recorded then Printf.printf "- %s %fs with %d calls\n" r.name r.time r.call in
  f time_generate_feature_vertex;
  f time_generate_subsumption_data;
  f time_implies;
  f time_ClauseSet_add;
  f time_ClauseSet_deactivate_implied_by;
  f time_ClauseSet_cleanup_deactivated;
  f time_ClauseSet_implies;
  f time_ClauseQueue_add;
  f time_ClauseQueue_get;
  f time_ClauseQueue_deactivate_implied_by;
  f time_ClauseQueue_implies;
  f time_ClauseQueue_cleanup_deactivated;
  f time_add_rule;
  f time_redundant_glob;
  f time_is_unselectable;
  f time_compo;
  f time_elim_and_tuple;
  f time_selection_fun;
  f time_transl_process;
  f time_check_feasible;
  f time_check_final_feasible;
  f time_simplify
