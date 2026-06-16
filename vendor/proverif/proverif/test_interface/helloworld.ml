(* ocamlfind ocamlc -g -package lablgtk2 -linkpkg helloworld.ml -o hello *)
open GMain
open GdkKeysyms
open Gobject.Data
let nb_max_proc = 1024

let cols = new GTree.column_list
let col_lst =
  let rec create_n_cols acc = function
    | 0 -> List.rev acc
    | n -> let col = cols#add string in create_n_cols (col::acc) (n - 1)
  in create_n_cols [] nb_max_proc

let data = ["Heinz El-Mann"; "Jane Doe"; "Joe Bungop"]

let data2 = [ "J"; "J"]

let create_model data =
  let store = GTree.list_store  cols  in
  let iter = store#append  () in
  let fill n proc =
    store#set ~row:iter ~column:(List.nth col_lst n) proc;
  in
  List.iteri fill data;
  store

let rec create_view ~model ~packing () =
  let view = GTree.view  ~model  ~packing   () in
  (* disable selection mode of rows *)
  (* view#selection#unselect_all (); *)
  view#selection#set_mode  `NONE;
  ignore(List.mapi (fun n d ->
    let col = GTree.view_column ~title:(List.nth data n) ~renderer:(GTree.cell_renderer_text [], ["text", List.nth col_lst n]) () in
    col#set_clickable true;
    ignore(col#connect#clicked ~callback:(fun () ->  call_fun view model packing));
    ignore (view#append_column col);
    col#set_resizable true;

    col
) data);
  view



and call_fun view model packing =
  let n_model = create_model data2 in
  let col = GTree.view_column ~renderer:(GTree.cell_renderer_text [], ["text", List.nth col_lst 3]) () in
  col#set_clickable true;
  ignore(col#connect#clicked ~callback:(fun () ->  call_fun view model packing));
  ignore (view#append_column col);
  col#set_resizable true;
  view#set_model (Some(n_model#coerce))
  (* view#set_model (Some (model)) *)


let locale = GtkMain.Main.init ()

(* let make_paneds n n_mess box = *)
(*   if n = 0 then *)
(*     let button = GButton.button ~label:(List.nth n_mess 0) ~packing:box#add () in *)
(*     button#connect#clicked ~callback:(fun () -> button#set_label "boum"); *)
(*   else *)
(*     let panedi = GPack.paned `HORIZONTAL ~width:1000  ~packing:box#add () in *)
(*     panedi#set_resize_mode `QUEUE; *)
(*     let button = GButton.button ~label:(List.nth n_mess 0) ~packing:panedi#add1() in *)
(*     button#connect#clicked ~callback:(fun () -> button#set_label "boum"); *)
(*     let first = ref true in *)
(*     let rec aux n n_mess paned = *)
(*       match n with *)
(*       | 1 -> *)

(*         (\* let paned = GPack.paned `HORIZONTAL ~packing:paned#add1 () in *\) *)
(*         (\* let button = GButton.button ~label:(List.nth n_mess 0) ~packing:paned#add1 () in *\) *)
(*         (\* button#connect#clicked ~callback:(fun () -> button#set_label "boum"); *\) *)
(*           let button = GButton.button ~label:(List.nth n_mess 0)   ~packing:paned#add2 () in *)
(*           button#connect#clicked ~callback:(fun () -> button#set_label "boum") *)
(*       | n -> *)
(*         let n_paned = GPack.paned `HORIZONTAL  ~packing:paned#add2 ()  in *)
(*         n_paned#set_resize_mode `QUEUE; *)
(*         let button = GButton.button ~label:(List.nth n_mess 0)  ~packing:n_paned#add1 () in *)
(*         button#connect#clicked ~callback:(fun () -> button#set_label "boum"); *)
(*         aux (n - 1) (List.tl n_mess) n_paned *)
(*     in *)
(*     aux (n ) (List.tl n_mess) panedi *)


let main () =
  (* Main windows *)
  let window_p = GWindow.window ~width:320 ~height:240
                              ~title:"Simple lablgtk program" () in

  (* Box to separate the menu for the content *)
  let box = GPack.vbox ~packing:window_p#add () in

  (* (\* Menu bar *\) *)
  let menubar = GMenu.menu_bar ~packing:box#pack () in
  let factory = new GMenu.factory menubar in
  let accel_group = factory#accel_group in
  let file_menu = factory#add_submenu "File" in

  (* (\* File menu *\) *)
  let factory = new GMenu.factory file_menu ~accel_group in
  factory#add_item "Quit" ~key:_Q ~callback: Main.quit;

  let window = GBin.scrolled_window ~packing:box#add () in

  let viewport = GBin.viewport ~packing:window#add () in

  let vbox = GPack.vbox ~packing:viewport#add () in
  window_p#connect#destroy ~callback:Main.quit;

  (* make_paneds 4 ["OhOh"; "HIHI"; "HUHU"; "HAHA";"HUHU"] vbox;  *)


let model = create_model data in
  let t = create_view ~model ~packing:vbox#add  () in


  (* Display the windows and enter Gtk+ main loop *)
  window_p#add_accel_group accel_group;
  window_p#show ();
  Main.main ()

let () = main ()
