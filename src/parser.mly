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
%token EQ COLONEQ
%token COMMA SEMICOLON
%token COLON 
%token BBAR 
%token DARROW ARROW INT BOOL THEN UNDERSCORE

(* constant tokens for rabbit *)
%token SYSTEM LEMMA TYPE ALLOW ATTACK INITCONST FILESYS CONSTANT EQUATION INSTRUCTION DOT SYSCALL 
%token CHANNEL TRANSFER PROCESS WITH FUNC MAIN RETURN 
%token DATA READ WRITE SEND RECV EAVESDROP TAMPER DROP
%token DATAGRAM STREAM SKIP LET CALL IF ELSE FOR IN RANGE AT INIT
%token REQUIRES SATISFIES SATISFY EXTERNAL STRING RABBIT EXTRACE ALLTRACE PATH

(* temporal logic *)
%token TRUE

(* End of input token *)
%token EOF

(* Precedence and fixity of infix operators *)
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
  | external_functions { $1 }
  | EQUATION x=expr EQ y=expr { DeclExtEq(x, y) }
  | TYPE id=NAME COLON c=type_c { DeclType(id,c) }
  
  | ALLOW ATTACK t=list(NAME) LBRACKET a=separated_nonempty_list(COMMA, NAME) RBRACKET { DeclAttack(t,a)}  
  | ALLOW s=NAME t=list(NAME) LBRACKET a=separated_nonempty_list(COMMA, NAME) RBRACKET { DeclAccess(s,t,a)} 

  | INITCONST t=NAME EQ e=expr SEMICOLON { DeclInit(t,e) }
  | FILESYS t=NAME EQ LBRACKET f=separated_nonempty_list(COMMA, fpath) RBRACKET { DeclFsys(t, f) }
  | CHANNEL id=NAME COLON n=NAME { DeclChan(id, n) }
  | PROCESS id=NAME LPAREN parems=separated_list(COMMA, NAME) RPAREN WITH ty=NAME 
    LBRACE l=let_stmts f=fun_decls m=main_stmt RBRACE { DeclProc(id, parems, ty, l, f, m) }
  
  | external_syscall { $1 }
  | external_attack { $1 }

  | sys { $1 }

external_functions:
  |  FUNC id=NAME COLON ar=NUMERAL { DeclExtFun(id, ar) }
  |  CONSTANT id=NAME  { DeclExtFun(id, 0) }

external_syscall:
  |  SYSCALL f=NAME LPAREN parems=separated_list(COMMA, typed_arg) RPAREN RETURN ret=expr COLON 
    r=separated_nonempty_list(DARROW, rule) { DeclExtSyscall(f, parems, r, Some ret) }
  |  SYSCALL f=NAME LPAREN parems=separated_list(COMMA, typed_arg) RPAREN COLON 
    r=separated_nonempty_list(DARROW, rule) { DeclExtSyscall(f, parems, r, None) }

external_attack:
  |  ATTACK f=NAME LPAREN parem=typed_arg RPAREN COLON r=rule { DeclExtAttack(f, parem, r) }


fact : mark_location(plain_fact) { $1 }
plain_fact:
  | scope=NAME COLON id=NAME LPAREN es=separated_list(COMMA, expr) RPAREN { LocalFact(scope, id, es) }
  | COLON id=NAME LPAREN es=separated_list(COMMA, expr) RPAREN { GlobalFact(id, es) }
  | id=NAME LPAREN es=separated_list(COMMA, expr) RPAREN { Fact(id, es) }


typed_arg:
  | var=NAME { (TyValue, var) }
  | CHANNEL var=NAME { (TyChannel, var) }
  | PROCESS var=NAME { (TyProcess, var) }
  | PATH var=NAME { (TyPath, var) }
  

rule:
  | LBRACKET precond=separated_list(COMMA, fact) RBRACKET ARROW LBRACKET postcond=separated_list(COMMA, fact) RBRACKET { (precond, postcond) }

sys:
  | SYSTEM p=separated_nonempty_list(BBAR, proc) REQUIRES 
    LBRACKET a=separated_nonempty_list(SEMICOLON, lemma) RBRACKET { DeclSys(p, a) }

proc: mark_location(plain_proc) { $1 }
plain_proc:
  | id=NAME LPAREN parems=separated_list(COMMA, NAME) RPAREN WITH f=NAME 
    { Proc (id, parems, f) }

lemma: mark_location(plain_lemma) { $1 }
plain_lemma:
  | LEMMA id=NAME COLON p=prop { Lemma (id, p) }

prop: mark_location(plain_prop) { $1 }
plain_prop:
  | EXTRACE QUOTED_STRING {PlainString ("exists-trace \""^$2^"\"") }
  | ALLTRACE QUOTED_STRING {PlainString ("all-trace \""^$2^"\"") }

let_stmts:
  | { [] }
  | l=let_stmt ls=let_stmts { l :: ls }

let_stmt:
  | LET id=NAME EQ e=expr SEMICOLON { (id, e) }

fun_decls:
  | { [] }
  | f = fun_decl fs=fun_decls { f :: fs }

fun_decl:
  | FUNC id=NAME LPAREN parems=separated_list(COMMA, NAME) RPAREN 
    LBRACE c=stmts RETURN r=NAME SEMICOLON RBRACE { (id, parems, c, r) }

main_stmt:
  | MAIN LBRACE c=stmts RBRACE { c }


fpath:
  | LBRACE PATH COLON fp=QUOTED_STRING COMMA DATA COLON e=expr COMMA TYPE COLON t=NAME RBRACE
    { (fp, e, t) }

(* mark_location(plain_fpath) { $1 }
plain_fpath: *)

type_c:
  | FILESYS { CFsys }
  | PROCESS { CProc }
  | CHANNEL { CChan }

attack_c:
  | EAVESDROP { CEaves }
  | TAMPER { CTamper }
  | DROP { CDrop }

chan_c:
  | DATAGRAM { CDatagram }
  | STREAM { CStream }

expr : mark_location(plain_expr) { $1 }
plain_expr:
  | id=NAME                    {   (Var (id)) }
  | b=BOOLEAN                  { Boolean b }
  | k=NUMERAL                  { Integer k }
  | r=FLOAT                    { Float r }
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

op : mark_location(plain_op) { $1 }
plain_op:
  | SKIP { Skip }
  | LET UNDERSCORE EQ e=expr { LetUnderscore (e) } 
  | LET id=NAME EQ e=expr { Let (id, e) }

block_op: mark_location(plain_block_op) { $1 }
plain_block_op:
  | IF LPAREN e=expr RPAREN LBRACE c1=stmts RBRACE 
    ELSE LBRACE c2=stmts RBRACE { If(e, c1, c2) }
  | FOR i=NAME IN RANGE LPAREN n=NUMERAL COMMA m=NUMERAL RPAREN 
    LBRACE c=stmts RBRACE { For(i,n,m,c) }

event : mark_location(plain_event) { $1 }
plain_event:
  | id=NAME LPAREN es=separated_list(COMMA, expr) RPAREN { Event(id, es) }

stmts: 
  | { [] }
  | s=stmt sl=stmts { s :: sl }

stmt: mark_location(plain_stmt) { $1 }
plain_stmt:
  | o=op SEMICOLON { OpStmt o }
  | o=block_op { OpStmt o }
  | o=op AT es=separated_list(COMMA, event) SEMICOLON { EventStmt (o, es) }

mark_location(X):
  x=X
  { Location.locate ~loc:(Location.make $startpos $endpos) x }
%%
