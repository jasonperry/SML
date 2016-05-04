open Fmtypes;

val decls: symtable * fdecl list = (
    [("x", FmInt), ("y", FmBool)], 
    [{fname="bar", argdecls=[], rettype=FmInt},
     {fname="baz", argdecls=[("x", FmInt), ("y", FmBool)], rettype=FmBool}])

val ex1 = ConstExpr 5
val ex2 = ConstBool true

val ex3 = CompExpr (Gt, (VarExpr "x"), (VarExpr "x"))

val ex4 = CompExpr (Gt, (VarExpr "x"), (VarExpr "y"))

val ex5 = CompExpr (Gt, (VarExpr "y"), (VarExpr "y"))

val ex6 = ArithExpr (Times, VarExpr "x", ConstExpr 3)

val ex7 = ArithExpr (Times, VarExpr "x", ConstExpr 3)

val ex8 = ArithExpr (Times, VarExpr "x", ConstExpr 3)

val ex9 = BoolExpr (And, ex3, ex3)

val ex10 = VarExpr "z"

val results = map (checkexpr decls) [ex1,ex2,ex3,ex4,ex5,ex6,ex7,ex8,ex9,ex10]

val ex11 = IfExpr (ex3, VarExpr "y", VarExpr "y")

val ex12 = IfExpr (ex3, VarExpr "y", VarExpr "x")

val ex13 = IfExpr (ex6, VarExpr "x", VarExpr "x")

val ex14 = FunCallExpr ("foo", [ConstExpr 7, VarExpr "y"])

val ex15 = FunCallExpr ("bar", [])

val ex16 = FunCallExpr ("baz", [ConstExpr 7, VarExpr "y"])

val ex17 = FunCallExpr ("baz", [ConstExpr 7, VarExpr "x"])

val ex18 = FunCallExpr ("baz", [ConstExpr 7, VarExpr "y", ConstExpr 8])

val ex19 = FunCallExpr ("baz", [ConstExpr 7])

val ex20 = FunCallExpr ("baz", [ConstBool true])
