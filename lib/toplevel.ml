(** A toplevel computation carries around the current environment. *)
type state =
  {
    desugar : Desugar.context;
    typecheck : Typecheck.context;
    runtime : Runtime.stack
  }

let initial = {
    desugar = Desugar.initial;
    typecheck = Typecheck.initial;
    runtime = Runtime.initial
}

let load_file ~quiet {desugar; typecheck; runtime} fn =
  let desugar, cmds = Desugar.load desugar fn in
  let typecheck, cmds = Typecheck.topfile typecheck cmds in
  let runtime = Eval.topfile ~quiet runtime cmds in
  {desugar; typecheck; runtime}
