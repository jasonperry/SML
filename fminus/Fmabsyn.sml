(* Fmabsyn.sml  -- the abstract syntax datatype *)

(* Some subtyping? Eq, Ord, Num, *)
datatype valtype = FmInt | FmBool | FmUnit (* | FmArray of valtype * int *)

fun typestr FmInt = "int" 
  | typestr FmBool = "bool"
  | typestr FmUnit = "unit"  

datatype storeclass = Indata | Outdata | Global | Local | Arg

type srcpos = int

(* If I don't keep source locations here, how can I typecheck 'later'? *)

datatype relop = Eq | Ne | Gt | Ge | Lt | Le
datatype arithop = Plus | Minus | Times | Div | Mod | Xor | Bitor | Bitand
datatype boolop = And | Or

(* TODO: hashtable indexed by name *)
type symentry = { name: string, vtype: valtype, sclass: storeclass }

type symtable = symentry list (* (string * valtype) list *)

datatype expr = ConstExpr of int
              | ConstBool of bool
              | VarExpr of string
              | NotExpr of expr
              | BoolExpr of boolop * expr * expr
              | CompExpr of relop * expr * expr
              | ArithExpr of arithop * expr * expr
              | IfExpr of expr * expr * expr
              | FunCallExpr of string * (expr list)

type texpr = expr * valtype

datatype stmt = AssignStmt of string * expr 
              | IfStmt of expr * sblock * sblock option
              | WhileStmt of expr * sblock
              | ForStmt of stmt * expr * stmt * sblock
              | PrintStmt of expr
              | CallStmt of string * expr list
              | ReturnStmt of expr option
              | BreakStmt of {pos: srcpos}
withtype sblock = symtable * stmt list

type fdecl = { fname: string, 
               argdecls: symentry list, (* (string * valtype) list, *)
               rettype: valtype }

type ftable = fdecl list

type fdefn = fdecl * sblock

(* Input/output data declarations, then globals *)
type progtext = { ddecls: symtable,
                  gdecls: symtable, 
                  fdefns: fdefn list, 
                  main: sblock option }
