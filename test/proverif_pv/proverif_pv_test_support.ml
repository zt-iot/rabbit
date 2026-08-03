let failwithf fmt = Printf.ksprintf (fun s -> prerr_endline s; failwith s) fmt
