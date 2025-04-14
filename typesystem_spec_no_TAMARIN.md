CONTENTS
==================================================================
1. FINAL GOAL OF THE TYPE SYSTEM
2. DEFINITION OF `is_sub`
3. DEFINITION OF `well_formed(t)`
4. DEFINITIONS OF `tenv` AND `typeof`
5. IMPLEMENTATION OF `typeof`
6. DEFINITION OF `typeof_f`
7. IMPLEMENTATION OF `typeof_f`
8. DEFINITION OF `well_typed_fact`
9. DEFINITION OF `well_typed` FUNCTION
10. IMPLEMENTATION OF `well_typed`
11. DEFINITION OF `typeof_p`
12. IMPLEMENTATION OF `typeof_p`




FINAL GOAL OF THE TYPE SYSTEM
------------------------------------------------------------------

* Let `p` be a closed process, meaning that p is a process with no free variables. `p` is the process representing our entire system
* Let `tenv` be a type environment such that `tenv` maps all variables and names to `U=(Public, Untrusted)`
* An opponent `o` is a process where all type annotations that appear are `U`

We want to show that:
`well_typed(p, tenv)` -> `p` preserves secrecy and integrity




DEFINITION OF `is_sub`
------------------------------------------------------------------
Subtyping: the exact same as in figure 3
Let `is_sub(t, t')` be an OCaml function that returns true if t is a subtype of `t'`


DEFINITION OF `well_formed(t)`
------------------------------------------------------------------
Well-formed types: the exact same as in figure 4
Let `well_formed(t)` be an OCaml function that returns true if Rabbit type t is well-formed

DEFINITIONS OF `tenv` AND `typeof`
------------------------------------------------------------------
Let `tenv` be a typing environment. It is a `Map` datastructure from `ID` to `t`, where `ID` is any Rabbit identifier and `t` is a Rabbit type
Let `typeof` be a function that takes a Rabbit term r and typing environment `tenv` and returns the Rabbit type for that raw term `r` under `tenv`


IMPLEMENTATION OF `typeof`
------------------------------------------------------------------

**(TRVar)**

* `mem x tenv = true`
_____________________________________________
`typeof(x, tenv) = find x tenv`


**(TRName)**
* `mem n tenv = true`
_____________________________________________
`typeof(n, tenv) = find n tenv`


**(TRSub)**

(Not sure how this would work...)

* `typeof(r, tenv) = t`
* `is_sub(t, t')`
_____________________________________________
`typeof(r, tenv) = t'`


**(TRPair)**

* `typeof(u, tenv) = t1`
* `typeof(v, tenv) = t2`
_____________________________________________
`typeof((u, v)) = (t1, t2)`

**(TRApp)**

* `typeof(id, tenv) = func[l, t_1, ..., t_n, ret]`
* `typeof(r_i, tenv) = t_i (* for all i from i to n *)`
_____________________________________________
`typeof(id(r_1, ..., r_n)) = ret  `


**(TRPack)**

* `well_typed(p, added((x, t), tenv))`
* `l = *any security level which we like*`
_____________________________________________
`typeof(pack(x, t, p)) = process[l, t]`


**(TTAnnot)**

(* Let's not bother with this rule for now, I don't think it's necessary *)



DEFINITION OF `typeof_f`
------------------------------------------------------------------
`typeof_f` takes a function signature with its body `p` and determines if the function's type annotation is correct


IMPLEMENTATION OF `typeof_f`
------------------------------------------------------------------

**(TPFunc)**

* There is a function `id(id_1 : t_1, ..., id_n : t_n): ret_ty { p }`
* `typeof_p(p, tenv \cup {id_1 : t_1, ..., id_n : t_n}) = ret_ty`                     (* THIS ASSUMES THAT PROCESSSES p RETURN A TYPE, WHICH IS CERTAINLY NOT TRIVIAL *)
__________________________________________________________________________________________
typeof_f(id, tenv) = func[l, t_1, ..., t_n, ret_ty]





DEFINITION OF `well_typed_fact`
------------------------------------------------------------------

Let `well_typed_fact(A, tenv)` be an OCaml function that returns true if TAMARIN Fact term `A` is well-typed under typing environment `tenv`.


DEFINITION OF `well_typed` FUNCTION
------------------------------------------------------------------
Let `well_typed(p, tenv)` be an OCaml function that returns true if Rabbit process `p` is well-typed under typing environment `tenv`, according to rules of Figure 5


IMPLEMENTATION OF `well_typed`
------------------------------------------------------------------

**(TPNil)**

_____________________________________________
well_typed(nil, tenv) = true                  (* nil denotes any process that has terminated *)

**(TPPar)**

well_typed(p, tenv) = true
well_typed(q, tenv) = true
_____________________________________________
well_typed(p | q, tenv) = true

**(TPRepl)**

well_typed(p, tenv) = true
_____________________________________________
well_typed(!p, tenv) = true


**(TPCase)**  

(* TPIfThenElse is replaced by TPCase *)
well_typed_fact(Aij, tenv) (* for all valid combinations of i, j)
well_typed(p_i, tenv) = t_i (* for all i from 1 to n *)
_____________________________________________
well_typed(case ([A11, ..., A1(m_1)] -> p_1, ..., [A_n1, ..., A_n(m_n)] -> p_n), tenv) (* m_i = how many facts there are in row i *)


**(TPNew)**

well_typed(p, added((n, t), tenv))
_____________________________________________
well_typed(new n : t in p, tenv)


(* TPIn, TPOut, TPSplit, TPSDec, TPADec are all replaced by well-typedness of function application *)

**(TPApp)**

typeof(r_i) = t_i
??????????????????
_____________________________________________
well_typed(id(r_1, ..., r_n))



**(TPVar)** 

(* New rule not in original type system *)
typeof(r, tenv) = t
well_typed(p, added((r, t), tenv))
_____________________________________________
well_typed(var x : t = r in p, tenv)


**(TPExec)**


typeof(u, tenv) = process[l, t]
typeof(v, tenv) = t
_____________________________________________
well_typed(exec(u, v), tenv)



DEFINITION OF `typeof_p`
------------------------------------------------------------------

Let `typeof_p(proc, tenv)` be a function that determines the return type of process `proc`
If `proc` only does side effects, `typeof_p(proc, tenv) = unit`


IMPLEMENTATION OF `typeof_p`
------------------------------------------------------------------

**(TChkR)**

typeof(r, tenv) = t
_____________________________________________
typeof_p(r, tenv) = t


**(TChkVar)**

_____________________________________________
typeof_p(var x : t = r in p, tenv) = typeof_p(p, tenv \union {(x : t)})


**(TChkAssign)**

_____________________________________________
typeof_p(x := r, tenv) = unit


**(TChkSeq)**

(* THIS RULE MIGHT CAUSE NAME RESOLUTION PROBLEMS IF NOT IMPLEMENTED CORRECTLY *)
_____________________________________________ 
typeof_p(p ; q,)
