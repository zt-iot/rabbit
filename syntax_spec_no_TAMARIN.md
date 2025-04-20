

REMOVED SYNTAX FROM RABBIT
------------------------------------------------------------------
* Equational theory
  * `function`
  * `equation`
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
Ident ::= ID                                                                                            (An [a-zA-Z]* string)

KeyKind ::= Sym | Enc | Dec | Sig | Chk                                                                 (Key kind)

SecrLevel ::= public | <Ident>.S                                                                        (Secrecy level declaration)
                                                                                                        ("id" should be a valid identifier referring to a process)
IntegLevel ::= untrusted | <Ident>.I                                                                     (Integrity level declaration)
                                                                                                        ("id" should be a valid identifier referring to a process)

SecLevel ::= (<SecrLevel>, <IntegLevel>)                                                                 (security level)
        
Type :: =             
  <SecLevel>                                                                                             (security level)
  | (<Type>, <Type>)                                                                                      (product)
  | channel[<SecLevel>, <Type>, <Type>]                                                                           (channel with security level l, read and write types t, t' respectively)
  | key[<SecLevel>, <KeyKind>, <Type>]                                                                            (key used on data of type t with security level l and key kind <KeyKind>. Only parties with correct secrecy level and integrity level can access the key)
  | process[<SecLevel>, <Type>]                                                                               (process with input parameter of type t and security level l)
  | func[<SecLevel>, <Type>*, <Type>]                                                                              (function with 0 or more input types t and one return type t (t=unit if f only does side effects), and security level l of the funcion code)


Variable ::= <Ident>
Name ::= <Ident>

RawTerm ::=          
<Variable>                                                                                               (variable, a binder for any raw term r)
| <Name>                                                                                             (name n. A name n can have any type and be used as such)
| (<RawTerm>, <RawTerm>)                                                                                        (pair)
| <Ident>(<RawTerm>*)                                                                                        (function application or syscall application)
                                                                                                (pk, vk, encryption, decryption, signing, hashing can all be implemented with functions)
| pack(<Ident> : <Type>, <ProcessTerm>)                                                         (x is variable, t is type, p is process term)
                                                                                                (not sure if this can be implemented with a function/syscall. The type t really needs to be explicitly given here)
        
Type-annotatedTerm ::=  <RawTerm> : <Type>                                                      (raw term r which has type t)
        
Fact ::=          
| <RawTerm> = <RawTerm>                                                                                          (equality checking between terms)
| <RawTerm> <> <RawTerm>                                                                        (Inequality checking)
        
ProcessTerm ::=            
0                                                                                               (nil process)
| <RawTerm>                                                                                             return raw term r
| var <Variable> : <Type> = <RawTerm> in <ProcessTerm>                                                                            (local variable declaration)
                                                                                                (r ::= f(r_1, ..., r_n) | s(r_1, ..., r_n)) //function or syscall calling is included in raw term
| <Variable> := <RawTerm>                                                                                        (mutation)
| <ProcessTerm> ; <ProcessTerm>                                                                                         (sequential composition)
| (<ProcessTerm> | <ProcessTerm>)                                                                                       (parallel composition)
| !<ProcessTerm>                                                                                            (replication)
| exec(<RawTerm>, <RawTerm>)                                                                                    (execute mobile process u with value v)
| new <Name> : <Type> in <ProcessTerm>                                                                                (name restriction when I is not given)
| case (| [<Fact>*] -> <ProcessTerm>)+ end                                                                     (case statement. If any set of facts A_i are all true holds, it consumes the facts A_i, i.e. removes them from the fact environment, and p is run)
                                                                                                (if multiple facts are true, one is chosen nondeterministically)
| repeat ([<Fact>*] -> <ProcessTerm>)+ until ([<Fact>*] -> <ProcessTerm>)+                                                        (if either lists of facts A* are true, consume them and do corresponding action p)



LoadDecl ::= load "<Identifier>"\n                                                                    (import functions from other file)

SyscallDecl ::= syscall <Ident>((<Ident>' : <Type>)*) { <ProcessTerm> }                                                  (syscall declaration)

TypeDecl ::= type <Ident> : <Type>                                                                     (type declaration)

SecLatticeRule ::= <SecrLevel> < <SecrLevel> | <IntegLevel> < <IntegLevel>

GlobalConst = const fresh <Ident> | const <Ident> = <RawTerm>                                                 (fresh nonce declaration or binding an expression r to an id globally)
Fun ::= function <Ident>((<Ident>' : <Type>)*): <Type> { <ProcessTerm> }                                             (function declaration inside of a process. Backticks represent the fact that keyword "function" should be written literally)
                                                                                                (Furthermore, enforce that a return type t' is given.)


MemoryDecl ::= var <Ident> : <Type> = <RawTerm>> \n                                                              (memory declaration. top-level variable "id" is available throughout the process and is initialized with raw term "r")
ProcDecl ::= process <Ident>((<Ident>' : <Type>)*) <MemoryDecl>* <Fun>* main() { <ProcessTerm> }                         (process declaration. id is process identifier)

RootProcDecl ::= process root((<Ident> : <Type>)*) <MemoryDecl>* <Fun>* main() { <ProcessTerm> }                     (There should be a single root process declaration)
                                                                                                (The other processes are then "mentioned" by the root process. We can think of these "mentions" as simple macro definitions)


Program ::= <LoadDecl>* <SyscallDecl>* <TypeDecl>* <SecLatticeRule>* <GlobalConst>* <ProcDecl>* <RootProcDecl>
```