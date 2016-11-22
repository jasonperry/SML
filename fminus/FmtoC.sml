(* Compile progtext to C *)

open Fmabsyn
open Fmtypes (* structure mode... *)
         
exception Unsupported of string

fun relopstring Eq = "=="
  | relopstring Ne = "!="
  | relopstring Gt = ">"
  | relopstring Ge = ">="
  | relopstring Lt = "<"
  | relopstring Le = "<="

fun arithopstring Plus = "+"
  | arithopstring Minus = "-"
  | arithopstring Times = "*"
  | arithopstring Div = "/"
  | arithopstring Mod = "%"
  | arithopstring Xor = "^"
  | arithopstring Bitor = "|"
  | arithopstring Bitand = "&"

fun joinwith _ []  = ""
  | joinwith _ [s] = s
  | joinwith inter (s::strs) = s ^ inter ^ (joinwith inter strs)

fun termwith inter [] = ""
(*  | termwith inter [s] = s ^ inter *)
  | termwith inter (s::strs) = s ^ inter ^ (termwith inter strs)

(* Storage class not used? If const, will change *)
fun printdecl {name, vtype, sclass} =  
  case vtype of
      FmInt => "int " ^ name
    | FmDouble => "double " ^ name 
    | FmBool => "bool " ^ name
    | _ => raise Unsupported ("Unsupported type: " ^ (typestr vtype))

fun printexpr (ConstExpr n) = Int.toString n
  | printexpr (ConstBool b) = if b then "1" else "0"
  | printexpr (ConstDouble d) = Real.toString d
  | printexpr (VarExpr v) = v
  | printexpr (NotExpr expr) = "!(" ^ printexpr expr ^ ")"
  | printexpr (BoolExpr (And, e1, e2)) =
    printexpr e1 ^ " && " ^ printexpr e2
  | printexpr (BoolExpr (Or, e1, e2)) =
    printexpr e1 ^ " || " ^ printexpr e2
  | printexpr (CompExpr (oper, e1, e2)) =
    printexpr e1 ^ " " ^ (relopstring oper) ^ " " ^ printexpr e2
  | printexpr (ArithExpr (oper, e1, e2)) =
    printexpr e1 ^ " " ^ (arithopstring oper) ^ " " ^ printexpr e2
  | printexpr (IfExpr (ifexpr, thenexpr, elseexpr)) =
    printexpr ifexpr ^ " ? " ^ printexpr thenexpr ^ " : "
    ^ printexpr elseexpr
  | printexpr (FunCallExpr (fname, elist)) =
    fname ^ "(" ^ joinwith ", " (map printexpr elist) ^ ")"

fun printstmt (AssignStmt (var, expr)) = var ^ " = " ^ printexpr expr ^ ";"
  | printstmt (IfStmt (cond, thenblk, elseopt)) =
    "if (" ^ printexpr cond ^ ")" ^ printsblock thenblk 
    ^ (if isSome elseopt
       then printsblock (valOf elseopt)
       else "")
  | printstmt (WhileStmt (cond, whileblk)) =
    "while (" ^ printexpr cond ^ ")" ^ printsblock whileblk
  | printstmt (ForStmt (init, cond, update, forblk)) =
    let val updstr = printstmt update
    in "for (" ^ printstmt init ^ printexpr cond ^ ";"
       (* shave off the semicolon *)
       ^ String.substring(updstr, 0, size updstr - 1)
       ^ ")" ^ printsblock forblk
    end
  | printstmt (PrintStmt expr) = 
      (case checkexpr expr of  (* Uses typechecker *)
           T FmBool => "printf(\"%s\\n\", " ^ printexpr expr
                       ^  " ? \"true\" : \"false\");"
         | T FmInt => "printf(\"%d\\n\", " ^ printexpr expr ^ ");"
         | T FmDouble => "printf(\"%f\\n\", " ^ printexpr expr ^ ");"
         | T t => raise Unsupported ("Unsupported type: " ^ (typestr t))
         | B errs => raise Unsupported ("Failed type check: "
                                        ^ (joinwith "\n" errs)) )
  (* | printstmt (PrintStmt expr) =
    "printf(\"%d\\n\"," ^ printexpr expr ^ ");" *)
  | printstmt (CallStmt (fname, elist)) =
    fname ^ "(" ^ joinwith ", " (map printexpr elist) ^ ");"
  | printstmt (ReturnStmt expropt) =
    "return" ^ (if isSome expropt
                then " " ^ printexpr (valOf expropt) ^ ";"
                else ";")
  | printstmt (BreakStmt {pos}) = "break;"

and printsblock (decls, stmts) = "{\n" ^
  termwith ";\n" (map printdecl decls) ^
  joinwith "\n" (map printstmt stmts) ^ "\n}\n"

fun printproc ({fname, argdecls, rettype}, body) =
  (case rettype of
       FmInt => "int "
     | FmDouble => "double "
     | FmBool => "bool "
     | _ => raise Unsupported ("Unsupported return type " ^
                               typestr rettype))
  ^ fname ^ "(" ^ joinwith ", " (map printdecl argdecls) ^ ")"
  ^ printsblock body

fun mapi f lst =
  let fun mapi' n [] = []
        | mapi' n (e::es) = (f (e,n))::(mapi' (n+1) es)
  in mapi' 0 lst
  end

fun printprog {ddecls, gdecls, fdefns, main} =
  (* Turn ddecls into command-line args *)
  let val arginits =
          concat (mapi (fn (entry:symentry, i) =>
                           "int " ^ #name entry
                           ^ " = atoi(argv[" ^ Int.toString (i+1)
                           ^ "]);\n") ddecls)
  in
      "#include <stdbool.h>\n#include<stdlib.h>\n#include <stdio.h>\n\n"
      ^ termwith ";\n" (map printdecl gdecls) ^ "\n"
      ^ joinwith "\n" (map printproc fdefns) ^ "\n"
      ^ (if isSome main (* more extra {{'s. *)
         then "void main (int argc, char** argv) {\n" ^ arginits
              ^ printsblock (valOf main) ^ "}\n"
         else "")
  end 
