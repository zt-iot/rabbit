(**************************************************************)
(* PROFILE.ML *)
(* Authors: Mark Hayden, 4/96; Bruno Blanchet 7/96 *)
(**************************************************************)
open Printf

let stdout_channel = stdout

open Unix
(**************************************************************)
let name = "PROFILE"
let failwith s = failwith (name^":"^s)
(**************************************************************)
(* BUG: fixed stack size *)

let profile = true

type prof_info = {
  name			: string ;
  mutable live 		: bool ;
  mutable self_ctr 	: int ;
  mutable total_ctr 	: int ;
  mutable ncalls 	: int
}

(**************************************************************)
let funcs = ref []
(**************************************************************)

let alloc_info name =
  let info = {
    name	= name ;
    live	= false ;
    self_ctr	= 0 ;
    total_ctr	= 0 ;
    ncalls	= 0
  } in	
  funcs := info :: !funcs ;
  info

(**************************************************************)

let start_time = ref None
and started    = ref false

external prof_start : unit -> unit = "start"
external prof_stop : unit -> int = "stop"
external push_stack : unit -> unit = "push_stack"
external pop_stack : prof_info -> unit = "pop_stack"

let start () =
  if profile then
  begin
     if !started then
        failwith "profiler started more than once" ;
     started := true ;
     let t = times() in
     start_time := Some (t.tms_utime +. t.tms_stime) ;
     prof_start()
  end

let stop () =
  if profile then
  begin
     if not !started then
        failwith "profile:stop:profiler not started" ;
     started := false ;
     let t = times() in
     let end_time = t.tms_utime +. t.tms_stime in
     let ticks = prof_stop() in

     let cmp i1 i2 = i2.self_ctr - i1.self_ctr in

     match !start_time with
     | Some(start_time) -> (
         let foi = float in
         let time = end_time -. start_time in
         let sample = time /. foi ticks in
         printf "  Number of samples is %d\n" ticks ;
         printf "  Each sample counts as %.3f seconds.\n\n" sample ;
         printf "  %%      self    self&            self     total\n" ;
         printf " time   seconds children   calls ms/call  ms/call  name\n" ;

         List.iter (fun info ->
	   if info.ncalls != 0 then
  	   printf "%5.2f %8.3f %8.3f %8d %7.2f %7.2f   %s\n"
	       (foi info.self_ctr /. foi ticks *. 100.0)
	       (foi info.self_ctr *. sample)
	       (foi info.total_ctr *. sample)
	       (info.ncalls)
	       (foi info.self_ctr *. sample /. foi info.ncalls *. 1000.)
	       (foi info.total_ctr *. sample /. foi info.ncalls *. 1000.)
	       (info.name)
         ) (List.sort cmp !funcs) ;
         printf "\n" ; flush stdout_channel
       )

     | _ -> failwith "sanity"
  end

(**************************************************************)

let f1 name f =
  if profile then
  begin
    let info = alloc_info name in
    fun a1 ->
      info.ncalls <- succ info.ncalls ;
      if info.live then (
        f a1
      ) else (
        info.live <- true ;
        push_stack();
        let res = try f a1 with x -> (
	  pop_stack(info);
  	  info.live <- false ;
	  raise x
        ) in
        pop_stack(info);
        info.live <- false ;
        res
      )
  end
  else f

(* copied from f1 *)
let f2 name f =
  if profile then
  begin
    let info = alloc_info name in
    fun a1 a2 ->
      info.ncalls <- succ info.ncalls ;
      if info.live then (
        f a1 a2
      ) else (
        info.live <- true ;
        push_stack();
        let res = try f a1 a2 with x -> (
  	pop_stack(info);
  	info.live <- false ;
  	raise x
        ) in
        pop_stack(info);
        info.live <- false ;
        res
      )
  end
  else f

(* copied from f1 *)
let f3 name f =
  if profile then
  begin 
    let info = alloc_info name in
    fun a1 a2 a3 ->
      info.ncalls <- succ info.ncalls ;
      if info.live then (
        f a1 a2 a3
      ) else (
        info.live <- true ;
        push_stack();
        let res = try f a1 a2 a3 with x -> (
  	pop_stack(info);
  	info.live <- false ;
  	raise x
        ) in
        pop_stack(info);
        info.live <- false ;
        res
      )
  end
  else f

(* copied from f1 *)
let f4 name f =
  if profile then
  begin   
    let info = alloc_info name in
    fun a1 a2 a3 a4 ->
      info.ncalls <- succ info.ncalls ;
      if info.live then (
        f a1 a2 a3 a4
      ) else (
        info.live <- true ;
        push_stack();
        let res = try f a1 a2 a3 a4 with x -> (
  	pop_stack(info);
  	info.live <- false ;
  	raise x
        ) in
        pop_stack(info);
        info.live <- false ;
        res
      )
  end
  else f

(* copied from f1 *)
let f5 name f =
  if profile then
  begin   
    let info = alloc_info name in
    fun a1 a2 a3 a4 a5 ->
      info.ncalls <- succ info.ncalls ;
      if info.live then (
        f a1 a2 a3 a4 a5
      ) else (
        info.live <- true ;
        push_stack();
        let res = try f a1 a2 a3 a4 a5 with x -> (
  	pop_stack(info);
  	info.live <- false ;
  	raise x
        ) in
        pop_stack(info);
        info.live <- false ;
        res
      )
  end
  else f

(* copied from f1 *)
let f6 name f =
  if profile then
  begin   
    let info = alloc_info name in
    fun a1 a2 a3 a4 a5 a6 ->
      info.ncalls <- succ info.ncalls ;
      if info.live then (
        f a1 a2 a3 a4 a5 a6
      ) else (
        info.live <- true ;
        push_stack();
        let res = try f a1 a2 a3 a4 a5 a6 with x -> (
  	pop_stack(info);
  	info.live <- false ;
  	raise x
        ) in
        pop_stack(info);
        info.live <- false ;
        res
      )
  end
  else f
