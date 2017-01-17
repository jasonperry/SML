(* Fmabsyn.sml  -- the abstract syntax datatype *)

(** These should probably be somewhere else...error checking and reporting.
  * However, srcpos does go in the tree *)
type srcpos = Location.Location
type errormsg = string * srcpos

(** These are data that will be inserted in symbol tables too. *) 
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

datatype relop = Eq | Ne | Gt | Ge | Lt | Le
(* TODO: bitwise not, shifts *)
datatype arithop = Plus | Minus | Times | Div | Mod | Xor | Bitand | Bitor
datatype boolop = And | Or

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

datatype decl =
         VarDecl of string * valtype (* multiples desugared by parser *)
         | ConstDecl of string * valtype * expr (* eval'ed at analysis *)
         | IODecl of string * valtype * storeclass (* known at parse time *)

(** for now, only statements can have position info--good compromise *)
datatype stree = 
         DeclStmt of decl (* These will be deleted on analysis *)
         | AssignStmt of string * expr (* Symentry ref here too?
                                        * lvalue type? *)
         | IfStmt of expr * sblock * sblock option
         | WhileStmt of expr * sblock
         | ForStmt of stmt * expr * stmt * sblock
         | PrintStmt of expr
         | CallStmt of expr (* string * expr list *) (* ftable ref? *)
         | ReturnStmt of expr option
         | BreakStmt
withtype stmt = {stree: stree, pos: srcpos}
     and sblock = (* symtable **) {stree: stree, pos: srcpos} list


type fdecl = { fname: string, 
               argdecls: symentry list, (* hmmm *)
               rettype: valtype,
               pos: srcpos }

type ftable = fdecl list

type fdefn = fdecl * sblock

(* Input/output data declarations, then globals *)
type progtext = { iodecls: decl list,  (* don't have to be stmts here *)
                  gdecls: decl list, (* addstoretype Global during anal. *)
                  fdefns: fdefn list, 
                  main: sblock option }

                                
(* Strings for types, for use in type checker messages *)
fun typestr FmInt = "int"
  | typestr FmDouble = "double"
  | typestr FmBool = "bool"
  | typestr FmUnit = "unit"
  | typestr Untyped = "**UNTYPED**" 
