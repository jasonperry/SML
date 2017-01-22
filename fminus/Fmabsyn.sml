(* Fmabsyn.sml  -- the abstract syntax datatype *)

(** ACTUAL ABSTRACT SYNTAX SECTION **)
(* structure Fmabsyn = struct *)

datatype relop = Eq | Ne | Gt | Ge | Lt | Le
(* TODO: bitwise not, shifts *)
datatype arithop = Plus | Minus | Times | Div | Mod | Xor | Bitand | Bitor
datatype boolop = And | Or

(** To give every expr a type accessible with #typ *)
datatype etree = ConstExpr of constval
(*               | ConstDouble of real
               | ConstBool of bool *)
               | VarExpr of string (* later: symentry ref? Nah. *)
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
         DeclStmt of decl list (* These will be deleted on analysis *)
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

(* type ftable = Funtable.symtable (* fdecl list *) *)

type fdefn = fdecl * sblock

(* Input/output data declarations, then globals *)
type progtext = { iodecls: decl list,  (* don't have to be stmts here *)
                  gdecls: decl list, (* addstoretype Global during anal. *)
                  fdefns: fdefn list,
                  gsyms: Symtable.symtable,
                  fsyms: Funtable.symtable,
                  main: sblock option }
   
(* end *)
