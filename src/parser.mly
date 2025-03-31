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
%token COMMA SEMICOLON COLON
%token BBAR
%token UNDERSCORE

(* constant tokens for rabbit *)
%token LOAD EQUATION CONSTANT CONST SYSCALL PASSIVE ATTACK ALLOW TYPE ARROW DARROW
%token CHANNEL PROCESS PATH DATA FILESYS 
%token WITH FUNC MAIN RETURN SKIP LET EVENT PUT CASE END BAR LT GT LTGT
%token SYSTEM LEMMA AT DOT DCOLON REPEAT UNTIL IN THEN ON VAR NEW DEL GET BY EXCL

%token REQUIRES EXTRACE ALLTRACE PERCENT FRESH LEADSTO REACHABLE CORRESPONDS

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
  |                                 { [] }
  | d=decl ds=decls       { d :: ds }

decl: mark_location(plain_decl) { $1 }
plain_decl:
  | FUNC id=NAME COLON ar=NUMERAL { DeclExtFun(id, ar) }
  | CONSTANT id=NAME  { DeclExtFun(id, 0) }
  | EQUATION x=expr EQ y=expr { DeclExtEq(x, y) }
  
  | TYPE id=NAME COLON c=type_c { DeclType(id,c) }
  
  | ALLOW ATTACK t=list(NAME) LBRACKET a=separated_nonempty_list(COMMA, NAME) RBRACKET { DeclAttack(t,a)}  
  | ALLOW s=NAME t=list(NAME) LBRACKET a=separated_nonempty_list(COMMA, NAME) RBRACKET { DeclAccess(s,t, Some a)} 
  | ALLOW s=NAME t=list(NAME) LBRACKET DOT RBRACKET { DeclAccess(s, t, None)} 

  | FILESYS t=NAME EQ LBRACKET f=separated_list(COMMA, fpath) RBRACKET { DeclFsys(t, f) }

  | CHANNEL id=NAME COLON n=NAME { DeclChan(id, n) }

  | PROCESS id=NAME LPAREN parems=separated_list(COMMA, colon_name_pair) RPAREN COLON ty=NAME 
    LBRACE l=let_stmts f=fun_decls m=main_stmt RBRACE { DeclProc(id, parems, ty, l, f, m) }

  | LOAD fn=QUOTED_STRING { DeclLoad(fn) }

  | CONST t=NAME EQ e=expr { DeclInit(t,Some e) }

  | CONST FRESH t=NAME { DeclInit(t,None) }

  | ATTACK f=NAME ON t=NAME LPAREN arg=separated_list(COMMA, typed_arg) RPAREN LBRACE c=cmd RBRACE { DeclExtAttack (f, t, arg, c) }

  | external_syscall { $1 }

  | sys { $1 }

  | CHANNEL id=NAME LT GT COLON n=NAME { DeclParamChan(id, n) }
  | CHANNEL id=NAME LTGT COLON n=NAME { DeclParamChan(id, n) }


  | CONST t=NAME LT p=NAME GT EQ e=expr { DeclParamInit(t, Some (p, e)) }

  | CONST FRESH t=NAME LT GT { DeclParamInit(t,None) }
  | CONST FRESH t=NAME LTGT { DeclParamInit(t,None) }



colon_name_pair :
  | a=NAME COLON b=NAME { (false, a, b) }
  | a=NAME LT GT COLON b=NAME { (true, a, b) }
  | a=NAME LTGT COLON b=NAME { (true, a, b) }

external_syscall:
  |  syscall_tk f=NAME LPAREN parems=separated_list(COMMA, typed_arg) RPAREN 
      LBRACE c=cmd RBRACE { DeclExtSyscall(f, parems, c) }

syscall_tk:
  | SYSCALL {()}
  | PASSIVE ATTACK {()}

fact : mark_location(plain_fact) { $1 }
plain_fact:
  | scope=NAME DCOLON id=NAME LPAREN es=separated_list(COMMA, expr) RPAREN { ChannelFact(scope, id, es) }
  | scope=NAME DOT id=NAME LPAREN es=separated_list(COMMA, expr) RPAREN { PathFact(scope, id, es) }
  | scope=NAME PERCENT id=NAME LPAREN es=separated_list(COMMA, expr) RPAREN { ProcessFact(scope, id, es) }
  | DCOLON id=NAME LPAREN es=separated_list(COMMA, expr) RPAREN { GlobalFact(id, es) }
  | id=NAME LPAREN es=separated_list(COMMA, expr) RPAREN { Fact(id, es) }
  | e1=expr EQ e2=expr { ResFact(0, [e1; e2]) }
  | e1=expr NEQ e2=expr { ResFact(1, [e1; e2]) }

typed_arg:
  | var=NAME { (TyValue, var) }
  | CHANNEL var=NAME { (TyChannel, var) }
  | PROCESS var=NAME { (TyProcess, var) }
  | PATH var=NAME { (TyPath, var) }

proc:
  | p=uproc { UnboundedProc p }
  | p=bproc { BoundedProc p}

sys:
  | SYSTEM p=separated_nonempty_list(BAR, proc) REQUIRES 
    LBRACKET a=separated_nonempty_list(SEMICOLON, lemma)  RBRACKET { DeclSys(p, a) }

uproc: mark_location(plain_uproc) { $1 }
plain_uproc:
  | id=NAME LPAREN parems=separated_list(COMMA, chan_arg) RPAREN WITH f=NAME 
    { Proc (id, parems, Some f) }
  | id=NAME LPAREN parems=separated_list(COMMA, chan_arg) RPAREN 
    { Proc (id, parems, None) }

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

let_stmts:
  | { [] }
  | l=let_stmt ls=let_stmts { l :: ls }

let_stmt:
  | VAR id=NAME EQ e=expr { (id, e) }

fun_decls:
  | { [] }
  | f = fun_decl fs=fun_decls { f :: fs }

fun_decl:
  | FUNC id=NAME LPAREN parems=separated_list(COMMA, NAME) RPAREN 
    LBRACE c=cmd RBRACE { (id, parems, c) }

main_stmt:
  | MAIN LBRACE c=cmd RBRACE { c }

fpath:
  | LBRACE PATH COLON fp=QUOTED_STRING COMMA DATA COLON e=expr COMMA TYPE COLON t=NAME RBRACE
    { (fp, e, t) }

(* mark_location(plain_fpath) { $1 }
plain_fpath: *)

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
  | VAR id=NAME EQ e=expr IN c=cmd { Let (id, e, c) }
  | id=uname COLONEQ e=expr { Assign (id, e) }
  | CASE 
    BAR? guarded_cmds=separated_nonempty_list(BAR, guarded_cmd) END { Case(guarded_cmds) }
  | REPEAT BAR? c1=separated_nonempty_list(BAR, guarded_cmd) 
    UNTIL BAR? c2=separated_nonempty_list(BAR, guarded_cmd) 
    END                                                             { While(c1, c2) }
  | EVENT LBRACKET a=separated_list(COMMA, fact) RBRACKET           { Event(a) }
  
  | LET ids=separated_list(COMMA, NAME) EQ e=expr DOT fid=NAME IN c=cmd { Get (ids, e, fid, c) }
  | NEW id=NAME EQ fid=NAME LPAREN args=separated_list(COMMA, expr) RPAREN IN c=cmd { New (id, fid, args, c) }
  | NEW id=NAME IN c=cmd { New (id, "", [], c) }
  | DEL e=expr DOT fid=NAME { Del (e, fid) }

  | e=expr { Return e }


uname: 
  | UNDERSCORE { None }
  | s=NAME { Some s }

mark_location(X):
  x=X
  { Location.locate ~loc:(Location.make $startpos $endpos) x }
%%
