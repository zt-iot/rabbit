let check condition message = if not condition then failwith message

let with_source source f =
  let filename = Filename.temp_file "rabbit_reduc_" ".rab" in
  Fun.protect
    ~finally:(fun () -> Sys.remove filename)
    (fun () ->
       Out_channel.with_open_text filename (fun oc -> output_string oc source);
       f filename)

let expect_error f =
  match f () with
  | _ -> failwith "Expected a source error"
  | exception Error.Error error -> error

let source = {|function enc:2
function dec:2
equation enc(x,k) = enc(x,k)
reduc dec(enc(x,k),k) = x
|}

let () =
  with_source source (fun filename ->
      let parsed, _ = Lexer.read_file Parser.file filename in
      (match List.map (fun (d : Input.decl) -> d.data) parsed with
       | [DeclExtFun _; DeclExtFun _; DeclExtEq _; DeclReduc (lhs, rhs)] ->
           (match lhs.data, rhs.data with
            | Apply ("dec", [_; _]), Var "x" -> ()
            | _ -> failwith "Reduction direction changed during parsing")
       | _ -> failwith "Reduction was not parsed as a distinct declaration");
      let env, decls = Typer.load (Env.init_env ()) filename in
      (match List.map (fun (d : Typed.decl) -> d.desc) decls with
       | [Function _; Function _; Equation _; Reduc (lhs, rhs)] ->
           (match lhs.desc, rhs.desc with
            | Apply (_, [{ desc = Apply (_, [{ desc = Ident { id = x; _ }; _ }; _]); _ }; _]),
              Ident { id = result; _ } ->
                check (x = result) "Reduction variables lost their shared binding"
            | _ -> failwith "Reduction direction changed during typing")
       | _ -> failwith "Reduction was not retained in the typed AST");
      let compiled, _, _ = Proverif_compiler.compile_program env decls in
      let open Rabbit_proverif_pv_parse.Pitptree in
      check (List.exists (function TReduc ([_], []) -> true | _ -> false) compiled)
        "Missing reduction declaration";
      check (not (List.exists (function
          | TFunDecl (("dec__0", _), _, _, _) -> true | _ -> false) compiled))
        "Destructor also declared as a constructor";
      let error = expect_error (fun () -> Sem.compile decls) in
      check (error.loc = (List.nth decls 3).loc) "Tamarin must reject the reduction at its source location";
      ignore (expect_error (fun () -> Loader.load filename Loader.process_init));
      with_source (Printf.sprintf "load %S\n" (Filename.basename filename))
        (fun importing ->
           let _, imported = Typer.load (Env.init_env ()) importing in
           check (List.exists (fun (d : Typed.decl) ->
               match d.desc with Reduc _ -> true | _ -> false) imported)
             "Loaded reduction disappeared"));
  List.iter (fun source ->
      with_source source (fun filename ->
          ignore (expect_error (fun () -> Typer.load (Env.init_env ()) filename))))
    [ "function f:1\nreduc f(x,x) = x\n"
    ; "reduc missing(x) = x\n"
    ; "function f:1\nreduc f(_) = x\n"
    ];
  with_source "function f:1\nreduc f(x) x\n" (fun filename ->
      ignore (expect_error (fun () -> Lexer.read_file Parser.file filename)))

let () =
  List.iter (fun (source, message) ->
      with_source source (fun filename ->
          let env, decls = Typer.load (Env.init_env ()) filename in
          let error = expect_error (fun () -> Proverif_compiler.compile_program env decls) in
          let actual = Format.asprintf "%t" (Error.print error) in
          check (try ignore (Str.search_forward (Str.regexp_string message) actual 0); true
                 with Not_found -> false) ("Unexpected diagnostic: " ^ actual)))
    [ "function f:1\nreduc x = f(x)\n", "left-hand side of reduc"
    ; "function f:1\nreduc f(x) = y\n", "All variables"
    ; "function f:1\nreduc f(f(x)) = x\n", "inside reduc arguments or results"
    ; "function f:1\nreduc f(x) = f(x)\n", "inside reduc arguments or results"
    ; "function f:1\nfunction g:1\nreduc f(g(x)) = x\nreduc g(x) = x\n",
      "inside reduc arguments or results"
    ; "function f:1\nfunction g:1\nreduc f(x) = g(x)\nreduc g(x) = x\n",
      "inside reduc arguments or results"
    ; "function f:1\nequation f(x) = x\nreduc f(x) = x\n", "constructor terms"
    ; "function f:1\nconst fresh secret\nreduc f(x) = secret\n", "Only variables"
    ; "function f:1\nreduc f(x) = x\nconst v = f(1)\n", "constructor terms"
    ];
  with_source {|function select:1
function a:1
reduc select(a(x)) = x
function b:1
reduc select(b(y)) = y
|} (fun filename ->
      let env, decls = Typer.load (Env.init_env ()) filename in
      let compiled, _, _ = Proverif_compiler.compile_program env decls in
      let open Rabbit_proverif_pv_parse.Pitptree in
      let relevant = List.filter_map (function
          | TFunDecl ((name, _), _, _, _) when name = "a__0" || name = "b__0" -> Some name
          | TReduc (rules, _) ->
              check (List.length rules = 2) "Reduction rules were not grouped";
              Some "reduc"
          | _ -> None) compiled in
      check (relevant = ["a__0"; "b__0"; "reduc"])
        "Reduction dependencies or declaration order are wrong")
