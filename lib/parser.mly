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
  | DATA st=ty { DeclSimpleTyp(st) } (* parse simple type *)

  
  | TYPE id=NAME COLON PROCESS { DeclProcType(id) }
  | TYPE id=NAME COLON FILESYS { DeclFileType(id) }
  | TYPE id=NAME COLON t=ty { DeclTyp(id, t) } (* channel type or security type declaration *)
  
  (* any function must have a return type (or unit) so 0-argument function also parses like this *)
  | FUNC id=NAME COLON params=separated_nonempty_list(ARROW, func_ty_param) { DeclEqThyFunc(id,  params) }

  | EQUATION x=expr EQ y=expr { DeclEqThyEquation(x, y) } (* Equational theory equation *)
  
  (* allow attack proc_ty+ [active_attacks+] *)
  | ALLOW ATTACK procs=list(NAME) LBRACKET attacks=separated_nonempty_list(COMMA, NAME) RBRACKET { DeclAllowAttack(procs, attacks) }  

  (* allow proc_ty <type>* [<syscall>*] *)
  | ALLOW proc=NAME ts=list(NAME) LBRACKET syscalls=separated_nonempty_list(COMMA, NAME) RBRACKET { DeclAccess(proc, ts, Some syscalls) }
  (* allow direct access with '[.]' *) 
  | ALLOW s=NAME t=list(NAME) LBRACKET DOT RBRACKET { DeclAccess(s, t, None)} 

  | CHANNEL id=NAME COLON t=ty { DeclChanInstantiation(id, t) }


  | PROCESS id=NAME LPAREN params=separated_list(COMMA, name_channel_pair) RPAREN COLON ty=NAME 
    LBRACE fl=file_stmts l=let_stmts f=fun_decls m=main_stmt RBRACE { DeclProc(id, params, ty, fl, l, f, m) }

  | PROCESS id=NAME LT process_param=NAME GT LPAREN params=separated_list(COMMA, name_channel_pair) RPAREN COLON ty=NAME 
    LBRACE fl=file_stmts l=let_stmts f=fun_decls m=main_stmt RBRACE { DeclParamProc(id, process_param, params, ty, fl, l, f, m) }


  | LOAD fn=QUOTED_STRING { DeclLoad(fn) }

  | CONST n=NAME COLON typ=ty EQ e=expr { DeclConst(n, typ, Some e) }

  | CONST FRESH n=NAME COLON typ=ty { DeclConst(n, typ, None) }

  
  | CONST FRESH c=NAME LT GT COLON typ=ty { DeclParamConst(c, typ, None) }
  | CONST FRESH c=NAME LTGT COLON typ=ty { DeclParamConst(c, typ, None) }
  | CONST c=NAME LT const_param=NAME GT COLON typ=ty EQ e=expr { DeclParamConst(c, typ, Some (const_param, e)) }
   
  (* TODO parse arguments as a suitable AST node instead of "NAME" *)
  | ATTACK f=NAME ON t=NAME LPAREN arg=separated_list(COMMA, NAME) RPAREN LBRACE c=cmd RBRACE { DeclExtAttack (f, t, arg, c) }

  | external_syscall { $1 }

  | sys { $1 }

  | CHANNEL id=NAME LT GT COLON t=ty { DeclParamChanInstantiation(id, t) }
  | CHANNEL id=NAME LTGT COLON t=ty { DeclParamChanInstantiation(id, t) }




name_channel_pair :
  | a=NAME COLON b=ty { (false, a, b) }
  | a=NAME LT GT COLON b=ty { (true, a, b) }
  | a=NAME LTGT COLON b=ty { (true, a, b) }


external_syscall_name_ty_param_pair : 
  | n=NAME COLON p=func_ty_param { (n, p) }

external_syscall:
  |  syscall_tk f=NAME LPAREN params=separated_list(COMMA, external_syscall_name_ty_param_pair) RPAREN 
      COLON retty=func_ty_param (* "COLON syscall_param" -> return type of syscall *)
      LBRACE c=cmd RBRACE { DeclExtSyscall(f, params, retty, c) }

syscall_tk:
  | SYSCALL {()}
  | PASSIVE ATTACK {()}

fact : mark_location(plain_fact) { $1 }
plain_fact:
  | scope=expr DCOLON id=NAME LPAREN es=separated_list(COMMA, expr) RPAREN { ChannelFact(scope, id, es) }
  | scope=expr PERCENT id=NAME LPAREN es=separated_list(COMMA, expr) RPAREN { ProcessFact(scope, id, es) }
  | DCOLON id=NAME LPAREN es=separated_list(COMMA, expr) RPAREN { GlobalFact(id, es) }
  | id=NAME LPAREN es=separated_list(COMMA, expr) RPAREN { Fact(id, es) }
  | e1=expr EQ e2=expr { ResFact(0, [e1; e2]) }
  | e1=expr NEQ e2=expr { ResFact(1, [e1; e2]) }
  | scope=expr DOT e=expr { ResFact(3, [scope; e]) }

// syscall_param:
//   | var=NAME { (TyValue, var) }
//   | CHANNEL var=NAME { (TyChannel, var) }
//   | PROCESS var=NAME { (TyProcess, var) }
//   | PATH var=NAME { (TyPath, var) }


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
  | FILE id=expr COLON ty=NAME EQ e=expr { (id, ty, e) }

let_stmts:
  | { [] }
  | l=let_stmt ls=let_stmts { l :: ls }

let_stmt:
  | VAR id=NAME COLON typ=ty EQ e=expr { (id, typ, e) }

fun_decls:
  | { [] }
  | f = fun_decl fs=fun_decls { f :: fs }

fun_decl:
  | FUNC id=NAME LPAREN parems=separated_list(COMMA, func_ty_param) RPAREN 
    LBRACE c=cmd RBRACE { (id, parems, c) }

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
  | S LPAREN p=func_ty_param RPAREN { S(p) }

func_param_integrity_lvl:
  | UNTRUSTED { Untrusted }
  | APOSTROPHE i=NAME { IntegPoly(i) }
  | I LPAREN p=func_ty_param RPAREN { I(p) }

func_ty_param : 
  | APOSTROPHE t=NAME { FuncParamPolyType(t) }
  | t=ty { FuncParamTyp(t, None, None) }
  | t=ty AT LPAREN s=func_param_secrecy_lvl COMMA i=func_param_integrity_lvl RPAREN { FuncParamTyp(t, Some s, Some i) }


(* A ty_param is either a polymorphic type or another simple type *)
ty_param :
  | APOSTROPHE t=NAME { ParamPolyType(t) }
  | t=NAME { ParamTyp(Typ(t, [])) }
  | t=NAME LBRACKET type_params=separated_nonempty_list(COMMA, ty_param) RBRACKET { ParamTyp(Typ(t, type_params)) }

ty:
  | UNIT { Unit }
  | CHANNEL LBRACKET typs=separated_nonempty_list(PLUS, ty) RBRACKET { ChannelTyp(typs) }

  (* First parse the situation where there are type parameters... *)
  | t=NAME LBRACKET type_params=separated_nonempty_list(COMMA, ty_param) RBRACKET { Typ(t, type_params) }
  (* Then the situation in which there are no type parameters... *)
  | t=NAME { Typ(t, []) }
  | t1=ty STAR t2=ty { ProdTyp(t1, t2) }


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
  | VAR id=NAME COLON typ=ty EQ e=expr IN c=cmd { Let (id, typ, e, c) }
  | id=uname COLONEQ e=expr { Assign (id, e) }
  | CASE 
    BAR? guarded_cmds=separated_nonempty_list(BAR, guarded_cmd) END { Case(guarded_cmds) }
  | REPEAT BAR? c1=separated_nonempty_list(BAR, guarded_cmd) 
    UNTIL BAR? c2=separated_nonempty_list(BAR, guarded_cmd) 
    END                                                             { While(c1, c2) }
  | EVENT LBRACKET a=separated_list(COMMA, fact) RBRACKET           { Event(a) }
  
  | LET ids=separated_list(COMMA, NAME) typ=ty EQ e=expr DOT fid=NAME IN c=cmd { Get (ids, typ, e, fid, c) }
  | NEW id=NAME COLON typ=ty EQ fid=NAME LPAREN args=separated_list(COMMA, expr) RPAREN IN c=cmd { New (id, typ, fid, args, c) }
  | NEW id=NAME COLON typ=ty IN c=cmd { New (id, typ, "", [], c) }
  | DEL e=expr DOT fid=NAME { Del (e, fid) }

  | e=expr { Return e }


uname: 
  | UNDERSCORE { None }
  | s=NAME { Some s }

mark_location(X):
  x=X
  { Location.locate ~loc:(Location.make $startpos $endpos) x }
%%
