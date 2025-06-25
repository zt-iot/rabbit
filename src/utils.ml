let run (com : string) : int * string list =
  Format.printf "execute %s@." com;
  let ic = Unix.open_process_in com in
  let outputs = In_channel.input_lines ic in
  let exit =
    match Unix.close_process_in ic with
    | WEXITED n -> n
    | _ -> assert false
  in
  exit, outputs

let runf fmt = Printf.ksprintf run fmt
