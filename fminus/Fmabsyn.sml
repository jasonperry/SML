(* Fmabsyn.sml  -- the abstract syntax datatype *)

(* Some subtyping? Eq, Ord, Num, *)
datatype valtype = FmInt | FmBool | FmUnit (* | FmArray of valtype * int *)

fun typestr FmInt = "int" 
  | typestr FmBool = "bool"
  | typestr FmUnit = "unit"  

(* If I don't keep source locations here, how can I typecheck 'later'? *)

datatype relop = Eq | Ne | Gt | Ge | Lt | Le
datatype arithop = Plus | Minus | Times | Div | Mod | Xor | Bitor | Bitand
datatype boolop = And | Or

type symtable = (string * valtype) list

datatype expr = ConstExpr of int
              | ConstBool of bool
              | VarExpr of string
              | NotExpr of expr
              | BoolExpr of boolop * expr * expr
              | CompExpr of relop * expr * expr
              | ArithExpr of arithop * expr * expr
              | IfExpr of expr * expr * expr
              | FunCallExpr of string * (expr list)

datatype stmt = AssignStmt of string * expr 
              | IfStmt of expr * sblock * sblock option
              | WhileStmt of expr * sblock
              | PrintStmt of expr
              | CallStmt of string * expr list
              | ReturnStmt of expr
withtype sblock = symtable * stmt list

type fdecl = { fname: string, 
               argdecls: symtable,
               rettype: valtype }

type fdefn = fdecl * sblock

type progtext = { gdecls: symtable, 
                  fdefns: fdefn list, 
                  main: sblock option }

