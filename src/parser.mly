%{
  open Input
%}

(* Infix operations a la OCaml *)
%token <Name.ident * Location.t> PREFIXOP INFIXOP0 INFIXOP1 INFIXOP2 INFIXOP3 INFIXOP4

(* Names and constants *)
%token <Name.ident> NAME
%token <Mpzf.t> NUMERAL
%token <string> FLOAT
%token <bool> BOOLEAN

(* Parentheses & punctuations *)
%token LPAREN RPAREN LBRACKET RBRACKET
%token EQ COLONEQ
%token COMMA SEMICOLON
%token COLON ARROW
%token BAR DARROW

(* constant tokens for acp *)
%token TY PROC FSYS CHAN 
%token ALLOW 
%token READ WRITE SEND RECV 
%token ATTACKERT EAVESDROP TAMPER DROP

(* constant tokens for initialization constants *)
%token INITCONST 

(* constant tokens for file system declaration *)
%token PATH DATA TYPE 

(* constant tokens for channel declarations *)
%token TRANSFER 

(* constant tokens for system instantiation *)
%token SYSTEM REQUIRES 

(* Datatypes & types *)
%token BOOL INT REAL
%token COMMAND

(* Commands *)
%token BEGIN END
%token SKIP TRACE
%token WHILE DO
%token CASE
%token IF THEN ELSE
%token LET VAR AND IN
%token LIM

(* Toplevel commands *)
%token <string> QUOTED_STRING
%token FUNCTION EXTERNAL
%token LOAD
%token PRECISION

(* End of input token *)
%token EOF

(* Precedence and fixity of infix operators *)
%nonassoc DARROW
%nonassoc IN
%right    SEMICOLON
%nonassoc ELSE
%left     INFIXOP0
%right    INFIXOP1
%left     INFIXOP2
%left     INFIXOP3
%right    INFIXOP4

%start <Input.decl list * Input.sys> file

%%

(* syntax *)

file:
  | f=decls s=sys EOF            { (f, s) }

sys: mark_location(plain_sys) { $1 }
plain_sys:
  | SYSTEM p=separated_nonempty_list(BBAR, proc) REQUIRES 
    LBRACKET a=separated_nonempty_list(SEMICOLON, assert) RBRACKET { Sys(p, a) }

proc: mark_location(plain_proc) { $1 }
plain_proc:
  | id=NAME LPAREN parems=separated_list(COMMA, NAME) RPAREN WITH f=NAME 
    { Proc (id, parems, f) }

assert: mark_location(plain_assert) { $1 }
plain_assert:
  | LEMMA id=NAME COLON p=prop { Assert (id, p) }

prop: mark_location(plain_prop) { $1 }
plain_prop:
  | TRUE {True}


  | DeclType of Name.ident * type_class
  | DeclAccess of Name.ident * Name.ident * (access_class list)
  | DeclAttack of Name.ident * (attack_class list)
  | DeclInit of Name.ident * expr
  | DeclFsys of Name.ident * ((Name.ident * expr * Name.ident) list)
  | DeclChan of Name.ident * chan_class
  | DeclProc of Name.ident * (Name.ident list) * Name.ident * ((Name.ident * expr) list) * (Name.ident * (Name.ident list) * comp) * comp 
type chan_class = CDatagram | CStream


decls:
  |                                 { [] }
  | d=decl ds=decls       { d :: ds }

decl: mark_location(plain_decl) { $1 }
plain_decl:
  | TYPE id=NAME COLON c=type_c { DeclType(id,c) }
  | ALLOW s=NAME t=NAME LBRACKET a=access_c RBRACKET { DeclAccess(s,t,a)} 
  | ATTACK t=NAME LBRACKET a=attack_c RBRACKET { DeclAttack(t,a)} 
  | INITCONST t=NAME EQ e=expr SEMICOLON { DeclInit(t,e) }
  | FILESYS t=NAME EQ LBRACKET f=separated_nonempty_list(COMMA, fpath) { DeclFsys(t, f) }
  | CHANNEL id=NAME EQ LBRACE TRANSFER COLON c=chan_c COMMA TYPE COLON n=NAME RBRACE { DeclChan(id, c, n) }
  | PROCESS id=name LPAREN parems=separated_list(COMMA, NAME) RPAREN WITH ty=NAME 
    LBRACE 
fpath: mark_location(plain_fpath) { $1 }
plain_fpath:
  | LBRACE PATH COLON fp=NAME COMMA DATA COLON e=expr COMMA TYPE COLON t=NAME RBRACE
    { Fpath(fp, e, t) }

type_c:
  | FILESYS { CFsys }
  | PROCESS { CProc }
  | CHANNEL { CChan }

access_c:
  | READ { CRead }
  | WRITE { CWrite }
  | SEND { CSend }
  | RECV { CRecv }

attack_c:
  | EAVESDROP { CEaves }
  | TAMPER { CTamper }
  | DROP { CDrop }

chan_c:
  | DATAGRAM { CDatagram }
  | STREAM { CStream }

accesses: 
  | a=access COMMA as=accesses {a :: as}
  | a=access {[a]}

access:
  | READ {TRead}
  | WRITE {TWrite}
  | SEND {TSend}
  | RECV {TRecv}

attacks: 
  | a=attack COMMA as=attacks {a :: as}
  | a=attack {[a]}

attack:
  | EAVESDROP {TEaves}
  | TAMPER {TTamper}
  | DROP {TDrop}


(* Toplevel directive. *)
topdirective: mark_location(plain_topdirective)      { $1 }
plain_topdirective:
  | LOAD fn=QUOTED_STRING                            { TopLoad fn }

(* Main syntax tree *)

term : mark_location(plain_term) { $1 }
plain_term:
  | e=plain_op_term                                             { e }
  | c1=term SEMICOLON c2=term                                   { Sequence (c1, c2) }
  | CASE lst=case_cases END                                     { Case lst }
  | IF e=op_term THEN c1=term ELSE c2=term END                  { If (e, c1, c2) }
  | WHILE e=op_term DO c=term END                               { While (e, c) }
  | LET a=separated_nonempty_list(AND,let_clause) IN c=term     { Let (a, c) }
  | VAR a=separated_nonempty_list(AND,var_clause) IN c=term     { Newvar (a, c) }
  | x=var_name COLONEQ e=op_term                                { Assign (x, e) }
  | LIM x=var_name DARROW e=term                                { Lim (x, e) }

op_term: mark_location(plain_op_term) { $1 }
plain_op_term:
  | e=plain_prefix_term                            { e }
  | e2=op_term oploc=infix e3=op_term
    { let (op, loc) = oploc in
      Apply (op, [e2; e3])
    }

prefix_term: mark_location(plain_prefix_term) { $1 }
plain_prefix_term:
  | e=plain_simple_term                        { e }
  | oploc=prefix e2=prefix_term
    { let (op, loc) = oploc in
      Apply (op, [e2])
    }
  | f=var_name LPAREN es=separated_list(COMMA, term) RPAREN
    { Apply (f, es) }

(* simple_term: mark_location(plain_simple_term) { $1 } *)
plain_simple_term:
  | x=var_name                 { Var x }
  | k=NUMERAL                  { Integer k }
  | r=FLOAT                    { Float r }
  | b=BOOLEAN                  { Boolean b }
  | SKIP                       { Skip }
  | TRACE                      { Trace }
  | LPAREN c=plain_term RPAREN { c }
  | BEGIN c=plain_term END     { c }

var_name:
  | NAME                     { $1 }
  | BOOL                     { "bool" }
  | REAL                     { "real" }
  | INT                      { "int" }
  | LPAREN op=infix RPAREN   { fst op }
  | LPAREN op=prefix RPAREN  { fst op }

%inline infix:
  | op=INFIXOP0    { op }
  | op=INFIXOP1    { op }
  | op=INFIXOP2    { op }
  | op=INFIXOP3    { op }
  | op=INFIXOP4    { op }

%inline prefix:
  | op=PREFIXOP { op }

case_cases:
  | BAR? lst=separated_nonempty_list(BAR, case_case)  { lst }

case_case:
  | e=op_term DARROW c=term  { (e, c) }

let_clause:
  | x=var_name EQ e=op_term  { (x, e) }

var_clause:
  | x=var_name COLONEQ e=op_term  { (x, e) }

fun_args:
  | xs=separated_list(COMMA, arg_decl) { xs }

arg_decl:
  | dt=datatype x=var_name { (x, dt) }

datatype:
  | BOOL { TBoolean }
  | INT  { TInteger }
  | REAL { TReal }

cmdty:
  | dt=datatype { TData dt }
  | COMMAND     { TCommand }

funty:
  | LPAREN dts=separated_list(COMMA, datatype) RPAREN ARROW t=cmdty
    { (dts, t) }

mark_location(X):
  x=X
  { Location.locate ~loc:(Location.make $startpos $endpos) x }
%%
