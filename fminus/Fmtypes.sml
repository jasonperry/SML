(* Typechecking functions *)

open Fmabsyn;

(** Typechecking function returns a type or a list of errors *)
datatype checkResult = T of valtype (* Stitch 'em like a monad? *)
                     | B of string list (* errors *)

(* should check decls and types in different fns? *)

(** takes pair (vdecls, fdecls) *)
(* TODO: replace with more efficient structure, using a memoizing 'maker' *)
fun lookup ([], _) sym = NONE
  | lookup ((e, vtype)::rest, _) sym =  
    if sym = e then SOME vtype
    else lookup (rest, []) sym

fun flookup (_, []) name = NONE
  | flookup (_, {fname, argdecls, rettype}::rest) name =
    if name = fname then SOME (argdecls, rettype) 
    else flookup ([], rest) name

fun checkexpr decls (ConstExpr i) = T FmInt
  | checkexpr decls (ConstBool b) = T FmBool
  | checkexpr decls (VarExpr var) = (case (lookup decls var) 
                                   of SOME t => T t
                                   |  NONE => B ["Undefined variable: " ^ var])
  | checkexpr decls (NotExpr expr) = (
      case (checkexpr decls expr)
       of B errs => B errs
        | T FmBool => T FmBool
        | T other => B ["Non-boolean type :" ^ (typestr other) ^ 
                        "in 'not' expression"])
  | checkexpr decls (BoolExpr (oper, e1, e2)) = 
    (case (checkexpr decls e1, checkexpr decls e2) 
      of (B err1, B err2) => B (err1 @ err2)
       | (B err1, T _) => B err1
       | (T _, B err2) => B err2
       | (T FmBool, T FmBool) => T FmBool
       | (T o1, T o2) => 
         B ["Non-boolean type : (" ^ (typestr o1) ^ "," ^
            (typestr o2) ^ ") in Boolean expression"])
  | checkexpr decls (CompExpr (oper, e1, e2)) = 
    (case (checkexpr decls e1, checkexpr decls e2) 
      of (B err1, B err2) => B (err1 @ err2)
       | (B err1, T _) => B err1
       | (T _, B err2) => B err2
       | (T t1, T t2) => 
         if t1 <> t2 
         then B ["Different types in comparison: (" ^
                 (typestr t1) ^ ", " ^ (typestr t2) ^ ")"]
         else (if (oper <> Eq andalso oper <> Ne) andalso t1 <> FmInt
               then B ["Ordered comparison of non-ordered type: " ^ typestr t1]
               else T FmBool) )
  | checkexpr decls (ArithExpr (oper, e1, e2)) = 
    (case (checkexpr decls e1, checkexpr decls e2) 
      of (B err1, B err2) => B (err1 @ err2)
       | (B err1, T _) => B err1
       | (T _, B err2) => B err2
       | (T FmInt, T FmInt) => T FmInt
       | (T t1, T t2) => if t1 <> t2
                         then B ["Incompatible types in arithmetic expr: (" ^ 
                                 (typestr t1) ^ ", " ^ (typestr t2) ^ ")"]
                         else B ["Non-numeric type in expression: " ^ (typestr t1)])
  | checkexpr decls (IfExpr (ifexp, thenexp, elsexp)) = 
    (case checkexpr decls ifexp (* Good candidate for monadization *)
      of B err => B err
      |  T iftype => 
         if iftype <> FmBool 
         then B ["Non-boolean type for test expression: " ^ typestr iftype]
         else (case checkexpr decls thenexp 
                of B err => B err
                 | T thentype => 
                   (case checkexpr decls elsexp
                     of B err => B err
                      | T elstype => 
                        if thentype <> elstype
                        then B ["Non-matching types (" ^ (typestr thentype) ^
                                ", " ^ (typestr elstype) ^ "for then/else"]
                        else T thentype)))
  | checkexpr decls (FunCallExpr (fname, fnargs)) = 
    (case flookup decls fname 
      of NONE => B ["Unrecognized function name: " ^ fname]
      |  SOME (params, rettype) => 
         let fun matchargs [] [] = [] (* List of errors in matching, empty if OK *)
               | matchargs (p::ps) [] = ["Not enough arguments to " ^ fname]
               | matchargs [] (p::ps) = ["Too many arguments to " ^ fname]
               | matchargs ((pname, ptype)::ps) (arg::args) = 
                 case checkexpr decls arg
                  of B errs => errs @ (matchargs ps args) (* Keep going *)
                  | T atype => if atype = ptype
                               then matchargs ps args
                               else "Non-matching argument types: (" ^ (typestr ptype) ^
                                    ", " ^ (typestr atype) :: (matchargs ps args)
         in
             case matchargs params fnargs
              of [] => T rettype
               | errs => B errs
         end)

(* Return list of errors *)
(* Only take closest matching name. If type doesn't match, then error. *)
(*fun checkblock gsyms fsyms args (lsyms, []) acc = acc
  | checkblock gsym fsyms args (lsyms, stmt::stmts) =
    let errs = case stmt
                of AssignStmt (var, expr) => (
                    case lookup (lsyms @ args @ gdecls) var 
                     of SOME type => checkexpr (lsyms @ args @ gdecls) 
                      | NONE => ["Assignment to undefined variable: " ^ var])
                 | IfStmt (expr, sblock,  => 
                           
                                                   

    in checkblock fsyms args (lsyms, stmts) (errs @ acc)
    end 
*)
(* Type errors data structure to 'flow' through this. *)
(* Need errors and previous function type declarations *)

(*fun typecheck {gdecls, fdecls, main} = 
  foldl checkfn [] fdecls
        where checkfn fsym { fname, argdecls, rettype, body=(lsyms, stmts) } = []
*)
