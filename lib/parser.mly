%{
  open Input
%}

(* Infix operations a la OCaml *)
%token <Name.ident * Location.t> PREFIXOP INFIXOP0 INFIXOP1 INFIXOP2 INFIXOP3 INFIXOP4

(* Names and constants *)
%token <Name.ident> NAME
%token <int> NUMERAL
%token <string> FLOAT
%token <bool> BOOLEAN
%token <string> QUOTED_STRING

(* Parentheses & punctuations *)
%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE 
%token COLONEQ EQ NEQ
%token COMMA SEMICOLON COLON APOSTROPHE PLUS STAR
%token BBAR
%token UNDERSCORE

(* constant tokens for rabbit *)
%token LOAD EQUATION CONSTANT CONST SYSCALL PASSIVE ATTACK ALLOW TYPE ARROW DARROW
%token CHANNEL PROCESS PATH DATA FILESYS FILE UNIT
%token WITH FUNC MAIN RETURN SKIP LET EVENT PUT CASE END BAR LT GT LTGT
%token SYSTEM LEMMA AT DOT DCOLON REPEAT UNTIL IN THEN ON VAR NEW DEL GET BY EXCL

%token REQUIRES EXTRACE ALLTRACE PERCENT FRESH LEADSTO REACHABLE CORRESPONDS

(* Secrecy and integrity levels within function typing signature *)
%token S I

(* Public and Untrusted for use in eqational theory typing signature *)
%token PUBLIC UNTRUSTED

(* End of input token *)
%token EOF

(* Precedence and fixity of infix operators *)
%nonassoc IN
%right    SEMICOLON

%left     INFIXOP0
%right    INFIXOP1
%left     INFIXOP2
%left     INFIXOP3
%right    INFIXOP4
%right    PREFIXOP

%start <Input.decl list> file

%%

(* syntax *)

file:
  | f=decls EOF            { f }
  
decls:
  |                       { [] }
  | d=decl ds=decls       { d :: ds }

decl: mark_location(plain_decl) { $1 }
plain_decl: 
  | DATA st=rabbit_ty { DeclSimpleTyp(st) } (* parse simple type *)

  
  | TYPE id=NAME COLON PROCESS { DeclProcType(id) }
  | TYPE id=NAME COLON FILESYS { DeclFileType(id) }
  | TYPE id=NAME COLON t=rabbit_ty { DeclTyp(id, t) } (* channel type or security type declaration *)
  
  
  | FUNC id=NAME COLON arity=NUMERAL { DeclEqThyFunc(id, Arity(arity)) }
  | FUNC id=NAME COLON params=separated_nonempty_list(ARROW, rabbit_ty) { DeclEqThyFunc(id, TypeSig(params)) }

  | EQUATION x=expr EQ y=expr { DeclEqThyEquation(x, y) } (* Equational theory equation *)
  
  (* allow attack proc_ty+ [active_attacks+] *)
  | ALLOW ATTACK procs=list(NAME) LBRACKET attacks=separated_nonempty_list(COMMA, NAME) RBRACKET { DeclAllowAttack(procs, attacks) }  

  (* allow proc_ty <type>* [<syscall>*] *)
  | ALLOW proc=NAME ts=list(NAME) LBRACKET syscalls=separated_nonempty_list(COMMA, NAME) RBRACKET { DeclAccess(proc, ts, Some syscalls) }
  (* allow direct access with '[.]' *) 
  | ALLOW s=NAME t=list(NAME) LBRACKET DOT RBRACKET { DeclAccess(s, t, None)}


  | CHANNEL id=NAME COLON t=rabbit_ty { DeclChanInstantiation(ChanParam{ id=id; param=None; typ=t} ) }
  | CHANNEL id=NAME LT GT COLON t=rabbit_ty { DeclChanInstantiation(ChanParam{id=id; param= Some (); typ=t}) }
  | CHANNEL id=NAME LTGT COLON t=rabbit_ty { DeclChanInstantiation(ChanParam{id=id; param= Some (); typ=t}) }



  | PROCESS id=NAME LT process_param=NAME GT LPAREN params=separated_list(COMMA, name_channel_pair) RPAREN COLON proc_typ=NAME 
    LBRACE fs=file_stmts ls=let_stmts mfs=member_fun_decls m=main_stmt RBRACE { 
      DeclProc{ id=id; is_process_parametric=Some(process_param); params=params; 
        proc_typ=proc_typ; file_stmts=fs; let_stmts=ls; funcs=mfs; main_func=m } 
    }

  | PROCESS id=NAME LPAREN params=separated_list(COMMA, name_channel_pair) RPAREN COLON proc_typ=NAME 
    LBRACE fs=file_stmts ls=let_stmts mfs=member_fun_decls m=main_stmt RBRACE { 
      DeclProc{ id=id; is_process_parametric=None; params=params; 
        proc_typ=proc_typ; file_stmts=fs; let_stmts=ls; funcs=mfs; main_func=m }  
    }

  


  | LOAD fn=QUOTED_STRING { DeclLoad(fn) }

  

  | CONST FRESH n=NAME COLON typ=rabbit_ty { DeclConst(n, Fresh, Some typ) }
  | CONST FRESH n=NAME { DeclConst(n, Fresh, None) }

  | CONST n=NAME COLON typ=rabbit_ty EQ e=expr { DeclConst(n, Value(e), Some typ) }
  | CONST n=NAME EQ e=expr { DeclConst(n, Value(e), None) }

  | CONST FRESH c=NAME LT GT COLON typ=rabbit_ty { DeclConst(c, Fresh_with_param, Some typ) }
  | CONST FRESH c=NAME LTGT COLON typ=rabbit_ty { DeclConst(c, Fresh_with_param, Some typ) }
  | CONST FRESH c=NAME LT GT { DeclConst(c, Fresh_with_param, None) }
  | CONST FRESH c=NAME LTGT { DeclConst(c, Fresh_with_param, None) }

  | CONST c=NAME LT const_param=NAME GT COLON typ=rabbit_ty EQ e=expr { DeclConst(c, Value_with_param(e, const_param), Some typ) }
  | CONST c=NAME LT const_param=NAME GT EQ e=expr { DeclConst(c, Value_with_param(e, const_param), None) }
   
  (* TODO parse arguments as a suitable AST node instead of "NAME" *)
  | ATTACK f=NAME ON t=NAME LPAREN arg=separated_list(COMMA, NAME) RPAREN LBRACE c=cmd RBRACE { DeclExtAttack (f, t, arg, c) }

  | external_syscall { $1 }

  | sys { $1 }

  




name_channel_pair :
  | a=NAME COLON typ=rabbit_ty { ChanParam{id=a; param=None; typ=typ} }
  | a=NAME LT GT COLON typ=rabbit_ty { ChanParam{id=a; param=Some (); typ=typ} }
  | a=NAME LTGT COLON typ=rabbit_ty { ChanParam{id=a; param=Some (); typ=typ} }



name_ty_param_pair : 
  | n=NAME COLON p=rabbit_ty { (n, p) }

(* function signature for syscalls and member functions *)
fun_signature:

  (* the case where there are zero parameters in between the (...) is handled separately 
  because otherwise this causes a Menhir reduce/reduce conflict *)
  | LPAREN RPAREN COLON retty=rabbit_ty { TypedSig([], [], retty) }
  | LPAREN RPAREN { UntypedSig([]) }

  | LPAREN names_and_types=separated_nonempty_list(COMMA, name_ty_param_pair) RPAREN 
      COLON retty=rabbit_ty { TypedSig(List.map fst names_and_types, List.map snd names_and_types, retty) }
  | LPAREN names=separated_nonempty_list(COMMA, NAME) RPAREN { UntypedSig(names) }



external_syscall:
  // |  syscall_tk f=NAME LPAREN params=separated_list(COMMA, name_ty_param_pair) RPAREN 
  //     COLON retty=rabbit_ty 
  //     LBRACE c=cmd RBRACE { DeclExtSyscall(f, List.map fst params, Some(List.map snd params), Some retty, c) }
  |  syscall_tk f=NAME signature=fun_signature
      LBRACE c=cmd RBRACE { DeclExtSyscall(f, signature, c) }

syscall_tk:
  | SYSCALL {()}
  | PASSIVE ATTACK {()}

fact : mark_location(plain_fact) { $1 }
plain_fact:
  | scope=expr DCOLON id=NAME LPAREN es=separated_list(COMMA, expr) RPAREN { ChannelFact(scope, id, es) }
  | scope=expr PERCENT id=NAME LPAREN es=separated_list(COMMA, expr) RPAREN { ProcessFact(scope, id, es) }
  | DCOLON id=NAME LPAREN es=separated_list(COMMA, expr) RPAREN { GlobalFact(id, es) }
  | id=NAME LPAREN es=separated_list(COMMA, expr) RPAREN { Fact(id, es) }
  | e1=expr EQ e2=expr { EqFact(e1, e2) }
  | e1=expr NEQ e2=expr { NeqFact(e1, e2) }
  | scope=expr DOT e=expr { FileFact(scope, e) }


sys:
  | SYSTEM p=separated_nonempty_list(BAR, proc) REQUIRES 
    LBRACKET a=separated_nonempty_list(SEMICOLON, lemma)  RBRACKET { DeclSys(p, a) }

proc:
  | p=uproc { UnboundedProc p }
  | p=bproc { BoundedProc p}

uproc: mark_location(plain_uproc) { $1 }
plain_uproc:
  | id=NAME LPAREN parems=separated_list(COMMA, chan_arg) RPAREN 
    { Proc (id, parems) }
  | id=NAME LT p=expr GT LPAREN parems=separated_list(COMMA, chan_arg) RPAREN 
    { ParamProc (id, p, parems) }

// bproc: mark_location(plain_bproc) { $1 }
bproc:
  | EXCL v=NAME DOT p=uproc { (v, [p]) }
  | EXCL v=NAME DOT LPAREN p=separated_list(BAR, uproc) RPAREN { (v, p) }


chan_arg:
  | id=NAME { ChanArgPlain id }
  | id=NAME LT GT { ChanArgParam id }
  | id=NAME LTGT { ChanArgParam id }
  | id=NAME LT e=expr GT { ChanArgParamInst (id, e) }

lemma: mark_location(plain_lemma) { $1 }
plain_lemma:
  | LEMMA id=NAME COLON p=prop { Lemma (id, p) }

prop: mark_location(plain_prop) { $1 }
plain_prop:
  | REACHABLE a=separated_nonempty_list(COMMA, fact) {Reachability (a)}
  | CORRESPONDS a=fact LEADSTO b=fact {Correspondence (a, b)}
  
  | EXTRACE QUOTED_STRING {PlainString ("exists-trace \""^$2^"\"") }
  | ALLTRACE QUOTED_STRING {PlainString ("all-traces \""^$2^"\"") }

file_stmts:
  | { [] }
  | l=file_stmt ls=file_stmts { l :: ls }

file_stmt:
  | FILE filepath=expr COLON file_ty=NAME EQ file_content=expr { (filepath, file_ty, file_content) }

let_stmts:
  | { [] }
  | l=let_stmt ls=let_stmts { l :: ls }

let_stmt:
  | VAR id=NAME COLON typ=rabbit_ty EQ e=expr { (id, e, Some typ) }
  | VAR id=NAME EQ e=expr { (id, e, None) }

member_fun_decls:
  | { [] }
  | f = member_fun_decl fs=member_fun_decls { f :: fs }

member_fun_decl:
  // | FUNC id=NAME LPAREN params=separated_list(COMMA, name_ty_param_pair) RPAREN 
  //   LBRACE c=cmd RBRACE { (id, List.map fst params, Some (List.map snd params), c) }
  | FUNC id=NAME signature=fun_signature 
    LBRACE c=cmd RBRACE { (id, signature, c) }

main_stmt:
  | MAIN LBRACE c=cmd RBRACE { c }

fpath:
  | LBRACE PATH COLON fp=QUOTED_STRING COMMA DATA COLON e=expr COMMA TYPE COLON t=NAME RBRACE
    { (fp, e, t) }

(* mark_location(plain_fpath) { $1 }
plain_fpath: *)







func_param_secrecy_lvl:
  | PUBLIC { Public }
  | APOSTROPHE s=NAME { SecPoly(s) }
  | S LPAREN p=rabbit_ty RPAREN { S(p) }

func_param_integrity_lvl:
  | UNTRUSTED { Untrusted }
  | APOSTROPHE i=NAME { IntegPoly(i) }
  | I LPAREN p=rabbit_ty RPAREN { I(p) }
  

plain_ty:
  | UNIT { Unit }
  (* First parse the situation where there are type parameters... *)
  | t=NAME LBRACKET type_params=separated_nonempty_list(COMMA, rabbit_ty) RBRACKET { PlainTyp(t, type_params) }
  (* Then the situation in which there are no type parameters... *)
  | t=NAME { PlainTyp(t, []) }

  | APOSTROPHE t=NAME { PolyType(t) }
  | CHANNEL LBRACKET typs=separated_nonempty_list(PLUS, rabbit_ty) RBRACKET { ChannelTyp(typs) }
  | t1=rabbit_ty STAR t2=rabbit_ty { ProdTyp(t1, t2) }

rabbit_ty:
  (* situation where there is an explicit security level *)
  | pt=plain_ty AT LPAREN s=func_param_secrecy_lvl COMMA i=func_param_integrity_lvl RPAREN { RabbitTyp(pt, Some(s, i)) }
  (* Situation where there is no explicit security level *)
  | pt=plain_ty { RabbitTyp(pt, None) }


type_c:
  | FILESYS { CFsys }
  | PROCESS { CProc }
  | CHANNEL { CChan }

expr : mark_location(plain_expr) { $1 }
plain_expr:
  | id=NAME                    { Var (id)  }
  | b=BOOLEAN                  { Boolean b }
  | k=NUMERAL                  { Integer k }
  | r=FLOAT                    { Float r   }
  | oploc=prefix e2=expr
    { let (op, loc) = oploc in
      Apply (op, [e2])
    }
  | f=NAME LPAREN es=separated_list(COMMA, expr) RPAREN
    { Apply (f, es) }
  | e2=expr oploc=infix e3=expr
    { let (op, loc) = oploc in
      Apply (op, [e2; e3])
    }
  | f=NAME LT e=expr GT { Param (f, e) }
  | LPAREN es=separated_list(COMMA, expr) RPAREN { Tuple es } 
  | s=QUOTED_STRING { String s }

%inline infix:
  | op=INFIXOP0    { op }
  | op=INFIXOP1    { op }
  | op=INFIXOP2    { op }
  | op=INFIXOP3    { op }
  | op=INFIXOP4    { op }

%inline prefix:
  | op=PREFIXOP { op }

guarded_cmd:
  | LBRACKET precond=separated_list(COMMA, fact) RBRACKET ARROW c=cmd { (precond, c) }

cmd: 
  | LBRACE c=cmd RBRACE { c }
  | mark_location(plain_cmd) { $1 } 
plain_cmd:
  | SKIP { Skip }
  | c1=cmd SEMICOLON c2=cmd { Sequence(c1, c2) }
  | PUT LBRACKET postcond=separated_list(COMMA, fact) RBRACKET { Put (postcond) }

  | VAR id=NAME COLON typ=rabbit_ty EQ e=expr IN c=cmd { Let (id, Some typ, e, c) }
  | VAR id=NAME EQ e=expr IN c=cmd { Let (id, None, e, c) }

  | id=uname COLONEQ e=expr { Assign (id, e) }
  | CASE 
    BAR? guarded_cmds=separated_nonempty_list(BAR, guarded_cmd) END { Case(guarded_cmds) }
  | REPEAT BAR? c1=separated_nonempty_list(BAR, guarded_cmd) 
    UNTIL BAR? c2=separated_nonempty_list(BAR, guarded_cmd) 
    END                                                             { While(c1, c2) }
  | EVENT LBRACKET a=separated_list(COMMA, fact) RBRACKET           { Event(a) }
  
  | LET ids=separated_list(COMMA, NAME) typ=rabbit_ty EQ e=expr DOT fid=NAME IN c=cmd { Get (ids, Some typ, e, fid, c) }
  | LET ids=separated_list(COMMA, NAME) EQ e=expr DOT fid=NAME IN c=cmd { Get (ids, None, e, fid, c) }

  | NEW id=NAME COLON typ=rabbit_ty EQ fid=NAME LPAREN args=separated_list(COMMA, expr) RPAREN IN c=cmd { 
      New (id, Some typ, Some(fid, args), c) 
    }
  | NEW id=NAME EQ fid=NAME LPAREN args=separated_list(COMMA, expr) RPAREN IN c=cmd {
      New (id, None, Some(fid, args), c)
    }
  | NEW id=NAME COLON typ=rabbit_ty IN c=cmd { 
      New (id, Some typ, None, c) 
    }
  | NEW id=NAME IN c=cmd {
      New (id, None, None, c)
    }
  | DEL e=expr DOT fid=NAME { Del (e, fid) }

  | e=expr { Return e }


uname: 
  | UNDERSCORE { None }
  | s=NAME { Some s }

mark_location(X):
  x=X
  { Location.locate ~loc:(Location.make $startpos $endpos) x }
%%
