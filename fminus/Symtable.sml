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

(** Find intersection of two symbol tables. *)
fun intersect (l1:symtable) ([]:symtable) = []
  | intersect [] l2 = []
  | intersect (e::rest) l2 =
    if isSome (lookup l2 (E.name e))
    then e::(intersect rest l2)
    else (intersect rest l2)

end

(* Possibly all this stuff in a file named "FmDefs" that everything depends
 * on. *)
type srcpos = Location.Location
type errormsg = string * srcpos

(** TYPE AND SYMBOL TABLE DECLARATIONS *)
(* Some subtyping? Eq, Ord, Num, *)
datatype valtype = FmInt | FmDouble | FmBool | FmUnit | Untyped
                   (* | FmArray of valtype * int *)
(* Strings for types, for use in type checker messages *)
fun typestr FmInt = "int"
  | typestr FmDouble = "double"
  | typestr FmBool = "bool"
  | typestr FmUnit = "unit"
  | typestr Untyped = "**UNTYPED**" 

(* What will I do when I want enumerated constants? Tags? *)
datatype constval = IntVal of int
                  | DoubleVal of real
                  | BoolVal of bool

(* TODO: add index type *)
datatype storeclass = Indata
                    | Outdata
                    | Global
                    | Local
                    | Arg
                    | Const (* DON'T keep value here *)

type symentry = { name: string, vtype: valtype, sclass: storeclass,
                 cval: constval option }

                  
(* Think we don't want opaque here. still want to use symentry on our own. *)
structure StEntry : ST_ENTRY = struct
    type entry = symentry
    fun name e = #name e
end

(* Note: SymtableFn must be visible (toplevel mode) *)
structure Symtable = SymtableFn (StEntry)

type fdecl = { fname: string, 
               argdecls: symentry list, (* because know everything now? *)
               rettype: valtype,
               pos: srcpos }

structure FtEntry : ST_ENTRY = struct
    type entry = fdecl
    fun name e = #fname e
end

structure Funtable = SymtableFn (FtEntry)
