open Fmtypes;

val vsyms = [("x", FmInt), ("y", FmBool)]
val argsyms = [("*return*", FmInt)]
val fdecls = [{fname="bar", params=[], rettype=FmInt},
              {fname="baz", params=[("x", FmInt), ("y", FmBool)], rettype=FmBool},
              {fname="noret", params=[("x", FmInt)], rettype=FmUnit}]

val stm1 = AssignStmt ("x", ConstExpr 5)
val stm2 = AssignStmt ("y", ConstBool false)
val stm3 = AssignStmt ("x", VarExpr "x")
val stm4 = AssignStmt ("x", ConstBool true)
val stm5 = AssignStmt ("y", ConstExpr 4)
val stm6 = AssignStmt ("y", CompExpr (Le, VarExpr "x", ConstExpr 5)) (* to bool! *)

val stm7 = IfStmt (VarExpr "y", ([], [AssignStmt ("x", ConstExpr 6)]), NONE) (* Boolean var *)
val stm8 = IfStmt (ConstExpr 42, ([], [AssignStmt ("x", ConstExpr 6)]), NONE)
val stm9 = IfStmt (CompExpr (Eq, VarExpr "y", ConstBool true),
                   ([], [AssignStmt ("x", ConstBool true)]),
                   NONE)
val stm10 = IfStmt (ConstExpr 42, ([], [AssignStmt ("x", ConstBool true)]), NONE)
(* errors in both then and else blocks *)
val stm11 = IfStmt (CompExpr (Eq, VarExpr "y", ConstBool true), (* Boolean equality *)
                    ([], [AssignStmt ("x", ConstBool true),
                          AssignStmt ("y", ConstExpr 7)]),
                   SOME ([], [AssignStmt ("x", ConstBool false)]))
(* err: ordered comparison of bool *)
val stm12 = IfStmt (CompExpr (Gt, VarExpr "y", ConstBool false), 
                    ([], [AssignStmt ("x", ConstBool true)]), NONE)

(* Call statements. *)
val stm13 = CallStmt ("noret", [VarExpr "x"])
(* Arg type mismatch *)
val stm14 = CallStmt ("noret", [VarExpr "y"])
val stm15 = CallStmt ("noret", [VarExpr "x", ConstExpr 5])
(* Discarding return value *)                     
val stm16 = CallStmt ("bar", [])

(* While Statements *)
val stm17 = WhileStmt (CompExpr (Ne, VarExpr "y", ConstBool false), 
                    ([], [AssignStmt ("x", VarExpr "x")]))
val stm18 = WhileStmt (CompExpr (Gt, VarExpr "y", ConstBool false), 
                    ([], [AssignStmt ("x", ConstExpr 87)]))
val stm19 = WhileStmt (CompExpr (Ne, VarExpr "y", ConstBool false), 
                       ([], [AssignStmt ("x", VarExpr "y")]))


(* Return statements *)
val stm20 = ReturnStmt (ArithExpr (Plus, VarExpr "x", ConstExpr 2))
val stm21 = ReturnStmt (CompExpr (Ge, VarExpr "x", ConstExpr 2))

val resgood = map (Fmtypes.checkstmt vsyms [] fdecls) [stm1, stm2, stm3, stm6, stm7]
val reserr = map (Fmtypes.checkstmt vsyms [] fdecls) [stm4, stm5, stm8]
