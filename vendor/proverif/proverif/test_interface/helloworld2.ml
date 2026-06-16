open GMain

let locale = GtkMain.Main.init ()

let rec callback () =
  let dialog = GWindow.dialog  ~modal:true ~width:320 ~height:240 () in
  (* let box = GPack.vbox ~packing:dialog#add () in *)
  let button = GEdit.entry ~packing:dialog#vbox#add () in
(* GtkFileProps.file_chooser  ~packing:dialog#vbox#add () in *)
  ();
  dialog#show()
  (* window#show() *)

let main () =
  let window_p = GWindow.window ~width:320 ~height:240
                              ~title:"Windows" () in
  let box = GPack.vbox ~packing:window_p#add () in
  let button = GButton.button ~label:"Button" ~packing:box#add () in
  ignore (button#connect#clicked ~callback:callback);
  window_p#show ();
  Main.main ()

let () = main ()
