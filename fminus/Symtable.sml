(* These could go in a .sig file, but not with mosml *)
signature ST_ENTRY = sig
    type entry
    val name : entry -> string
end

signature SYMTABLE = sig
    type symentry
    type symtable

    val empty: symtable
    val maketable: symentry list -> symtable (* necessary? *)
    val insert: symtable -> symentry -> symtable
    val lookup: symtable -> string -> symentry option
    val merge: symtable -> symtable -> symtable
    val intersect: symtable -> symtable -> symtable
end

(** Do I really need a signature for a symbol table? *)
functor SymtableFn (E:ST_ENTRY) : SYMTABLE = struct

type symentry = E.entry

(* Possibly replace with binary tree or somesuch. *)
type symtable = symentry list

val empty: symtable = []

fun maketable symlist = symlist

fun insert (tab: symtable) e = e::tab

(** Look up in variable symbol table *)
(* TODO: replace with more efficient structure, using a memoizing 'maker' *)
fun lookup ([]:symtable) symname = NONE
  | lookup (e::rest) symname = 
    if E.name e = symname then SOME e
    else lookup rest symname

(** Look up in function name symbol table *)
(* fun flookup ([]:ftable) name = NONE
  | flookup ((entry as {fname, argdecls, rettype, pos})::rest) name =
    if name = fname then SOME entry
    else flookup rest name *)

fun merge (t1:symtable) (t2:symtable) = t1 @ t2

(** Find intersection of two symbol tables. *)
fun intersect (l1:symtable) ([]:symtable) = []
  | intersect [] l2 = []
  | intersect (e::rest) l2 =
    if isSome (lookup l2 (E.name e))
    then e::(intersect rest l2)
    else (intersect rest l2)

end
