

REMOVED SYNTAX FROM RABBIT
------------------------------------------------------------------
* structure creation via `new x = I(e_1, ..., e_n)` and `get`
* `delete e`
* system instantiation
* filesystems and paths
* requires, lemma
* attack (passive and active)
* allow proc_ty ch_ty [o] (decides which processes are allowed to access which channels)
* allow attack (...)
__________________________________________________________________

```
Ident ::= ID                                                                                            (An [a-zA-z_\-]* string)


Variable ::= <Ident>
Name ::= <Ident>

Expr ::=          
<Variable>                                                                                               (variable, a binder for any raw term r)
| <Name>                                                                                             (name n. A name n can have any type and be used as such)
| (<Expr>, <Expr>)                                                                                        (pair)
                                                                                        (pk, vk, encryption, decryption, signing, hashing can all be implemented with functions)

TypeKind ::= channel | process | filesys                                            (kinds of types)
        
Fact ::= 
  FACT                                                                                          (any valid TAMARIN fact)
        


Cmd ::=            
| <Expr>                                                                                             return raw term r
| var <Variable> = <Expr> in <Cmd>                                                                            (local variable declaration)
                                                                                                (r ::= f(r_1, ..., r_n) | s(r_1, ..., r_n)) //function or syscall calling is included in raw term
| <Variable> := <Expr>                                                                                        (mutation)
| <Variable> := f(<Expr>*)                                                                      (function/syscall application)
| <Cmd> ; <Cmd>                                                                                         (sequential composition)
| new <Name> in <Cmd>                                                                          (name restriction when I is not given)
| new <Name> = Q(<Expr>+)                                                                      (create new structure Q with arguments e_1, ..., e_n)
| delete <Expr>                                                                                 (delete structure when given expression refers to an address containing a structure Q)
| put [<Fact>]                                                                                  (puts <Fact> in the fact environment)
| case (| [<Fact>*] -> <Cmd>)+ end                                                                     (case statement. If any set of facts A_i are all true holds, it consumes the facts A_i, i.e. removes them from the fact environment, and p is run)
                                                                                                (if multiple facts are true, one is chosen nondeterministically)
| repeat ([<Fact>*] -> <Cmd>)+ until ([<Fact>*] -> <Cmd>)+                                                        (if either lists of facts A* are true, consume them and do corresponding action p)




LoadDecl ::= load "<Ident>"\n                                                                    (import Rabbit code from other file)



SyscallDecl ::= syscall <Ident>(<Ident>*) { <Cmd> }                                                  (syscall declaration. Functions which might perform side effects)


SyscallId = . | <Ident>*                                                            (`.` is any system call)
AllowRule ::= allow <Ident> <Ident> [SyscallId]                                       (processes of type t1 are allowed to access channels of type t2 via system call id)

PassiveAttack ::= passive attack <Ident>(<Ident>*) { <Cmd> }                              (passive attacks add arbitrary computations <Cmd> whenever called)
ActiveAttack ::= attack <Ident> on <Ident>(<Ident>*) { <Cmd> }                            (active attacks modify the result of system calls)
AttackDecls ::= <PassiveAttack>* <ActiveAttack>*

AllowPassiveAttack ::= allow <Ident> [<PassiveAttack>*]                            (Any process of type <Ident> may be affected by the attack)
AllowActiveAttack ::= allow attack <Ident> [<ActiveAttack>*]                       (Any process of type <Ident> may be affected by the attack)
AllowAttackDecls ::=  <AllowPassiveAttack>* <AllowActiveAttack>* 




TypeKindDecl ::= type <Ident> : <TypeKind>                                          (Declares that <Ident> is of kind <TypeKind>)


GlobalConst = const fresh <Ident> | const <Ident> = <Expr>                                                 (fresh nonce declaration or binding an expression r to an id globally)
Fun ::= function <Ident>(<Ident>*){ <Cmd> }                                             (function declaration inside of a process. Backticks represent the fact that keyword "function" should be written literally)
                                                                                                (Furthermore, enforce that a return type t' is given.)


MemoryStmt ::= var <Ident> = <Expr> \n                                                              (memory declaration. top-level variable "id" is available throughout the process and is initialized with raw term "r")
ProcDecl ::= process <Ident>((<Ident> : <Ident>)*) : <Ident> { <MemoryStmt>* <Fun>* main() { <Cmd> } }              (process declaration. Each <Ident> : <Ident> is a pair of an identifier with a TypeKind. ": <Ident>" denotes the TypeKind of the process )


SystemInstantiation = system <blah1> requires <blah2> 


EqFuncDecl ::= function <Ident> : <Numeral>                                                        
                                                                                                    
EquationDecl ::= equation <Expr> = <Expr>                                                       (<Expr> should both be equational theory function applications)
EquationalTheory ::= (<EqFuncDecl> | <EquationDecl>)*

RabbitProgram ::= <EquationalTheory> <LoadDecl>* <SyscallDecl>* <TypeKindDecl>* <AttackDecls> <AllowAttackDecls> <GlobalConst>* <ProcDecl>* <SystemInstantiation>
```
