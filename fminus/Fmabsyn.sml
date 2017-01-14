(* Fmabsyn.sml  -- the abstract syntax datatype *)

(* Should these be here or somewhere else? 
 * They're more related to checking and reporting than to types proper.
 * Although the tree does have srcpos's in it. *)
type srcpos = Location.Location
type errormsg = string * srcpos

(* Some subtyping? Eq, Ord, Num, *)
datatype valtype = FmInt | FmDouble | FmBool | FmUnit | Untyped
                   (* | FmArray of valtype * int *)

datatype constval = IntVal of int
                  | DoubleVal of real
                  | BoolVal of bool

(* TODO: add index type *)
datatype storeclass = Indata
                    | Outdata
                    | Global
                    | Local
                    | Arg
                    | Const of constval (* just keep value here *)

(* If I don't keep source locations here, how can I typecheck 'later'? *)

datatype relop = Eq | Ne | Gt | Ge | Lt | Le
(* TODO: bitwise not, shifts *)
datatype arithop = Plus | Minus | Times | Div | Mod | Xor | Bitand | Bitor
datatype boolop = And | Or

(* TODO: hashtable indexed by name *)
type symentry = { name: string, vtype: valtype, sclass: storeclass }

type symtable = symentry list

(** To give every expr a type accessible with #typ *)
datatype etree = ConstInt of int
               | ConstDouble of real
               | ConstBool of bool
               | VarExpr of string (* later: symentry ref? *)
               | NotExpr of expr
               | BoolExpr of boolop * expr * expr
               | CompExpr of relop * expr * expr
               | ArithExpr of arithop * expr * expr
               | IfExpr of expr * expr * expr
               | FunCallExpr of string * expr list
(* should have (etree, PROPS of {typ, pos}) pair? *)
withtype expr = {etree: etree, typ: valtype, pos:srcpos}

(** for now, only statements can have position info--good compromise *)
datatype stree = AssignStmt of string * expr (* Symentry ref here too?
                                             * lvalue type? *)
               | IfStmt of expr * sblock * sblock option
               | WhileStmt of expr * sblock
               | ForStmt of stmt * expr * stmt * sblock
               | PrintStmt of expr
               | CallStmt of expr (* string * expr list *) (* ftable ref? *)
               | ReturnStmt of expr option
               | BreakStmt
withtype stmt = {stree: stree, pos: srcpos}
     and sblock = symtable * {stree: stree, pos: srcpos} list


type fdecl = { fname: string, 
               argdecls: symentry list,
               rettype: valtype,
               pos: srcpos }

type ftable = fdecl list

type fdefn = fdecl * sblock

(* Input/output data declarations, then globals *)
type progtext = { ddecls: symtable,
                  gdecls: symtable, 
                  fdefns: fdefn list, 
                  main: sblock option }

(*** SYMBOL TABLE FUNCTIONS ***)

(** Look up in variable symbol table *)
(* TODO: replace with more efficient structure, using a memoizing 'maker' *)
fun vlookup ([]:symtable) sym = NONE
  | vlookup ((entry as {name, vtype, sclass})::rest) sym = 
    if name = sym then SOME entry
    else vlookup rest sym

(** Look up in function name symbol table *)
fun flookup ([]:ftable) name = NONE
  | flookup ((entry as {fname, argdecls, rettype, pos})::rest) name =
    if name = fname then SOME entry
    else flookup rest name

(** Find intersection of two symbol tables. *)
fun intersect_syms l1 [] = []
  | intersect_syms [] l2 = []
  | intersect_syms ((entry as {name, vtype, sclass})::es) l2 =
    if isSome (vlookup l2 name)
    then entry::(intersect_syms es l2)
    else (intersect_syms es l2)
                                
(* Strings for types, for use in type checker messages *)
fun typestr FmInt = "int"
  | typestr FmDouble = "double"
  | typestr FmBool = "bool"
  | typestr FmUnit = "unit"
  | typestr Untyped = "**UNTYPED**" 

                        
(** Attempt to reduce an expression to a constval *)
(* ? Should have a separate const datatype? *)
fun evalConstExp syms (e as {etree, typ=_, pos=_}: expr) =
  case etree
   of ConstInt n => SOME (IntVal n)
    | ConstDouble d => SOME (DoubleVal d)
    | ConstBool b => SOME (BoolVal b)
    | VarExpr v => (
        case vlookup syms v
         of SOME {name=_, vtype=_, sclass=(Const cval)} => SOME cval
          | SOME _ => NONE
          | NONE => NONE (* don't bother throwing error here *) )
    | NotExpr e => (
        case evalConstExp syms e
         of SOME (BoolVal b) => SOME (BoolVal (not b))
          | SOME _ => NONE
          | NONE => NONE )
    | BoolExpr (oper, e1, e2) => ((
        case (oper, valOf (evalConstExp syms e1), valOf (evalConstExp syms e2))
         of (And, BoolVal b1, BoolVal b2) => SOME (BoolVal (b1 andalso b2))
          | (Or, BoolVal b1, BoolVal b2) => SOME (BoolVal (b1 orelse b2))
          | _ => NONE )
                                  handle Option => NONE )
    | CompExpr (oper, e1, e2) => ((
        case (oper, valOf (evalConstExp syms e1), valOf (evalConstExp syms e2))
         of (Eq, IntVal i1, IntVal i2) => SOME (BoolVal (i1 = i2))
          | (Eq, BoolVal b1, BoolVal b2) => SOME (BoolVal (b1 = b2))
          | (Ne, IntVal i1, IntVal i2) => SOME (BoolVal (i1 <> i2))
          | (Ne, BoolVal b1, BoolVal b2) => SOME (BoolVal (b1 <> b2))
          | (Gt, IntVal i1, IntVal i2) => SOME (BoolVal (i1 > i2))
          | (Gt, DoubleVal d1, DoubleVal d2) => SOME (BoolVal (d1 > d2))
          | (Ge, IntVal i1, IntVal i2) => SOME (BoolVal (i1 >= i2))
          | (Ge, DoubleVal d1, DoubleVal d2) => SOME (BoolVal (d1 >= d2))
          | (Lt, IntVal i1, IntVal i2) => SOME (BoolVal (i1 < i2))
          | (Lt, DoubleVal d1, DoubleVal d2) => SOME (BoolVal (d1 < d2))
          | (Le, IntVal i1, IntVal i2) => SOME (BoolVal (i1 <= i2))
          | (Le, DoubleVal d1, DoubleVal d2) => SOME (BoolVal (d1 <= d2))
          | _ => NONE)
                                  handle Option => NONE )
    | ArithExpr (oper, e1, e2) => ((
        case (oper, valOf (evalConstExp syms e1), valOf(evalConstExp syms e2))
         of (Plus, IntVal i1, IntVal i2) => SOME (IntVal (i1 + i2))
          | (Plus, DoubleVal d1, DoubleVal d2) => SOME (DoubleVal (d1 + d2))
          | (Minus, IntVal i1, IntVal i2) => SOME (IntVal (i1 - i2))
          | (Minus, DoubleVal d1, DoubleVal d2) => SOME (DoubleVal (d1 - d2))
          | (Times, IntVal i1, IntVal i2) => SOME (IntVal (i1 * i2))
          | (Times, DoubleVal d1, DoubleVal d2) => SOME (DoubleVal (d1 * d2))
          | (Div, IntVal i1, IntVal i2) => SOME (IntVal (i1 div i2))
          | (Div, DoubleVal d1, DoubleVal d2) => SOME (DoubleVal (d1 / d2))
          | (Mod, IntVal i1, IntVal i2) => SOME (IntVal (i1 mod i2))
            (* watch out for precision loss. MosML defaults to 63 bits *)
          | (Xor, IntVal i1, IntVal i2) =>
            SOME (IntVal (Word.toInt (Word.xorb
                                          (Word.fromInt i1, Word.fromInt i2))))
          | (Bitand, IntVal i1, IntVal i2) =>
            SOME (IntVal (Word.toInt (Word.andb
                                          (Word.fromInt i1, Word.fromInt i2))))
          | (Bitor, IntVal i1, IntVal i2) =>
            SOME (IntVal (Word.toInt (Word.orb
                                          (Word.fromInt i1, Word.fromInt i2))))
          | _ => NONE )
                                   handle Option => NONE )
    | IfExpr (condexp, thenexp, elseexp) => (
        case evalConstExp syms condexp
         of SOME (BoolVal b) => if b then evalConstExp syms thenexp
                                else evalConstExp syms elseexp
          | _ => NONE )
    | FunCallExpr _  => NONE (* If it's pure and the args are constants... *)


