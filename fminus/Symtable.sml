
(* TODO: hashtable indexed by name *)
type symentry = { name: string, vtype: valtype, sclass: storeclass,
                  cval: constval option }

(* TODO: Abstract datatype for symbol table *)
type symtable = symentry list

(*** SYMBOL TABLE FUNCTIONS ***)

(** Look up in variable symbol table *)
(* TODO: replace with more efficient structure, using a memoizing 'maker' *)
fun vlookup ([]:symtable) sym = NONE
  | vlookup ((entry as {name, ...})::rest) sym = 
    if name = sym then SOME entry
    else vlookup rest sym

(** Look up in function name symbol table *)
fun flookup ([]:ftable) name = NONE
  | flookup ((entry as {fname, argdecls, rettype, pos})::rest) name =
    if name = fname then SOME entry
    else flookup rest name

(** Find intersection of two symbol tables. *)
fun intersect_syms (l1:symtable) ([]:symtable) = []
  | intersect_syms [] l2 = []
  | intersect_syms ((entry as {name, ...})::es) l2 =
    if isSome (vlookup l2 name)
    then entry::(intersect_syms es l2)
    else (intersect_syms es l2)
