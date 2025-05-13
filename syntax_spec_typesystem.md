

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

Anything between `<!--` and `-->` should not be considered part of the language currently
```
Ident ::= ID                                                                                            (An [a-zA-z_\-]* string)

KeyKind ::= Sym | Enc | Dec | Sig | Chk                                                                 (Key kind)

SecrecyLvl ::= public | <Ident>.S | S(<Type>)                                                                       (Secrecy level declaration)
                                                                                                    (Example: <Ident> ::= tee || <Ident> ::= ree etc.)
                                                                                                        ("id" should be a valid identifier referring to a process)
                                                                                                        S(<Type>) retrieves the secrecy level of a given type
IntegrityLvl ::= untrusted | <Ident>.I | I(<Type>)                                                                     (Integrity level declaration)
                                                                                                        (<Ident> must be a valid identifier referring to a process)

SecurityLvl ::= (<SecrecyLvl>, <IntegrityLvl>)                                                                 (security level)
        
Type :: =             
  <SecurityLvl>                                                                                             (security level)
                                                                                                          (NOTE: U is syntactic sugar for (public, untrusted))
  | '<Ident>                                                                                              (Polymorphic type)
  | S'<Ident>                                                                                             (Polymorphic SecrecyLvl)
  | I'<Ident>                                                                                             (Polymorphic IntegrityLvl)
  | SI'<Ident>                                                                                            (Polymorphic SecurityLvl)
  | (<Type>, <Type>)                                                                                      (product)
  | channel[<SecurityLvl>, <Type>, <Type>]                                                                           (channel with security level l, read and write types t, t' respectively)
  | key[<SecurityLvl>, <KeyKind>, <Type>]                                                                            (key used on data of type t with security level l and key kind <KeyKind>. Only parties with correct secrecy level and integrity level can access the key)
  | process[<SecurityLvl>, <Type>?]                                                                               (process with input parameter of type t and security level l)
  | function[<SecurityLvl>, <Type>*, <Type>]                                                                              (function with 0 or more input types t and one return type t, t=unit if f only does side effects, and security level l of the funcion code)
  | string                                                                                                    (a plain quoted string)
  


Variable ::= <Ident>
Name ::= <Ident>

RawTerm ::=          
<Variable>                                                                                               (variable, a binder for any raw term r)
| <Name>                                                                                             (name n. A name n can have any type and be used as such)
| (<RawTerm>, <RawTerm>)                                                                                        (pair)
| <Ident>(<RawTerm>*)                                                                                        (function application or syscall application)
                                                                                                (pk, vk, encryption, decryption, signing, hashing can all be implemented with functions)
<!-- | pack(<Ident> : <Type>, <ProcessTerm>)                                                         (x is variable, t is type, p is process term) -->
                                                                                                (not sure if this can be implemented with a function/syscall. The type t really needs to be explicitly given here)
        
Type-annotatedTerm ::=  <RawTerm> : <Type>                                                      (raw term r which has type t)
        
Fact ::=          
| <RawTerm> = <RawTerm>                                                                                          (equality checking between terms)
| <RawTerm> <> <RawTerm>                                                                        (Inequality checking)
| <Ident>::store(<Ident>)                                                                       (name stored on a channel)
        
ProcessTerm ::=            
0                                                                                               (nil process)
| <RawTerm>                                                                                             return raw term r
| var <Variable> : <Type> = <RawTerm> in <ProcessTerm>                                          (typed local variable declaration)
| var <Variable> = <RawTerm> in <ProcessTerm>                                                   (untyped local variable declaration)
                                                                                              
| <Variable> := <RawTerm>                                                                                        (mutation)
| <ProcessTerm> ; <ProcessTerm>                                                                                         (sequential composition)
<!-- | (<ProcessTerm> | <ProcessTerm>)                                                                                       (parallel composition) -->
<!-- | !<ProcessTerm>                                                                                            (replication) -->
<!-- | exec(<RawTerm>, <RawTerm>)                                                                                    (execute mobile process u with value v) -->
| new <Name> : <Type> in <ProcessTerm>                                                                          (typed name restriction when structure Q is not given)
| new <Name> in <ProcessTerm>                                                                          (untyped name restriction when structure Q is not given)
| put [<Fact>]                                                                                                  (puts <Fact> in the fact environment)
| case (| [<Fact>*] -> <ProcessTerm>)+ end                                                                     (case statement. If any set of facts A_i are all true holds, it consumes the facts A_i, i.e. removes them from the fact environment, and p is run)
                                                                                                (if multiple facts are true, one is chosen nondeterministically)
| repeat ([<Fact>*] -> <ProcessTerm>)+ until ([<Fact>*] -> <ProcessTerm>)+                                                        (if either lists of facts A* are true, consume them and do corresponding action p)




LoadDecl ::= load "<Ident>"\n                                                                    (import Rabbit code from other file)

SyscallDecl ::= syscall <Ident>((<Ident> : <Type>)*) { <ProcessTerm> }                           (typed syscall declaration. Functions which might perform side effects)

TypeDecl ::= type <Ident> : <Type>                                                                     (type declaration)

SecLatticeRule ::= <SecrecyLvl> < <SecrecyLvl> | <IntegrityLvl> < <IntegrityLvl>

GlobalConst = const fresh <Ident> : <Type> | const <Ident> : <Type> = <RawTerm>                                                 (fresh nonce declaration or binding an expression r to an id globally)
Fun ::= function <Ident>((<Ident> : <Type>)*): <Type> { <ProcessTerm> }                                             (function declaration inside of a process. Backticks represent the fact that keyword "function" should be written literally)
                                                                                                (Furthermore, enforce that a return type t' is given.)


MemoryStmt ::= var <Ident> : <Type> = <RawTerm> \n                                                              (memory declaration. top-level variable "id" is available throughout the process and is initialized with raw term "r")
ProcDecl ::= process <Ident>((<Ident> : <Type>)*) : <Type> { <MemoryStmt>* <Fun>* main() { <ProcessTerm> } }                         (process declaration. id is process identifier)

RootProcDecl ::= process root((<Ident> : <Type>)*) : <Type> { <MemoryStmt>* <Fun>* main() { <ProcessTerm> } }                     (There should be a single root process declaration)
                                                                                                (The other processes are then "mentioned" by the root process. We can think of these "mentions" as simple macro definitions)





EqFuncDecl ::= function <Ident>((<Ident> : <Type>)*) : <Type>                                                       (Functions which do not perform side effects <Ident> is in the second pair of brackets "()" to make it more readable what the function does)
                                                                                                    (Due to a technicality for hash, we require the `[()]?`)
EquationDecl ::= equation <RawTerm> = <RawTerm>
EquationalTheory ::= (<EqFuncDecl> | <EquationDecl>)*

RabbitLibraryProgram ::= <EquationalTheory> <LoadDecl>* <SyscallDecl>* <TypeDecl>* <GlobalConst>* <ProcDecl>* <RootProcDecl>
RabbitMainProgram ::= <EquationalTheory> <LoadDecl>* <SyscallDecl>* <TypeDecl>* <SecLatticeRule>* <GlobalConst>* <ProcDecl>* (* security lattice is all defined in main Rabbit program file *)
```
