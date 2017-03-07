(* These could go in a .sig file, but not with mosml *)
signature ST_ENTRY = sig
    type entry
    val name : entry -> string
    val toString : entry -> string
end

(** Do I really need a specified signature for a symbol table? *)
signature SYMTABLE = sig
    (* type symentry *)
    (* structure E: ST_ENTRY *)
    type symentry (*= E.entry  (* Allowed! Now will be visible? *)*)
    type symtable

    val empty: symtable
    val fromList: symentry list -> symtable
    val insert: symtable -> symentry -> symtable
    val lookup: symtable -> string -> symentry option
    val merge: symtable -> symtable -> symtable
    val intersect: symtable -> symtable -> symtable
    val toString: symtable -> string
end

(** Not an opaque constraint because symentries need to be inspected. *)
functor SymtableFn (E:ST_ENTRY) :> SYMTABLE where type symentry = E.entry
= struct

type symentry = E.entry (* redundant, but needed to match *)

(* Possibly replace with binary tree or somesuch. *)
type symtable = E.entry list

val empty: symtable = []

fun fromList symlist = symlist

fun insert (tab: symtable) e = e::tab

(** Look up in variable symbol table *)
(* TODO: replace with more efficient structure, using a memoizing 'maker' *)
fun lookup ([]:symtable) symname = NONE
  | lookup (e::rest) symname = 
    if E.name e = symname then SOME e
    else lookup rest symname

fun merge (t1:symtable) (t2:symtable) = t1 @ t2

(** Find intersection of two symbol tables. *)
fun intersect (l1:symtable) ([]:symtable) = []
  | intersect [] l2 = []
  | intersect (e::rest) l2 =
    if isSome (lookup l2 (E.name e))
    then e::(intersect rest l2)
    else (intersect rest l2)


fun toString [] = "\n"
  | toString (sym::syms) = E.toString sym ^ "; " ^ (toString syms)

end (* functor SymtableFn *)

(*
(* Tests for opacity issue *)
structure Myentry : ST_ENTRY = struct
  type entry = {name: string, typ: string}
  fun name (e:entry) = #name e
  fun typ (e:entry) = #typ e               
end

(* SML/NJ requires parentheses for the functor application, mosml doesn't *)
structure Mytable = SymtableFn (Myentry)
val tab = Mytable.insert (Mytable.empty) ({name="x", typ="str"})
*)
