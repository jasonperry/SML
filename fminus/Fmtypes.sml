(* Typechecking functions *)

open Fmabsyn;

(** Typechecking function returns a type or a list of errors *)
datatype checkResult = T of valtype (* Stitch 'em like a monad? *)
                     | B of string list (* errors *)

(* should check decls and types in different fns? *)

(*** SYMBOL TABLE FUNCTIONS ***)
                                   
(* TODO: replace with more efficient structure, using a memoizing 'maker' *)
fun vlookup [] sym = NONE
  | vlookup ((e, vtype)::rest) sym = 
    if sym = e then SOME vtype
    else vlookup rest sym

fun flookup ([] : fdecl list) name = NONE
  | flookup ({fname, argdecls, rettype}::rest) name =
    if name = fname then SOME (argdecls, rettype) 
    else flookup rest name

fun intersect_syms l1 [] = []
  | intersect_syms [] l2 = []
  | intersect_syms ((k,v)::es) l2 =
    if isSome (vlookup l2 k)
    then (k,v)::(intersect_syms es l2)
    else (intersect_syms es l2)


(*** SEMANTIC CHECKING FUNCTIONS ***)
             
fun checkexpr (decls: symtable * fdecl list) (ConstExpr i) = T FmInt
  | checkexpr _ (ConstBool b) = T FmBool
  | checkexpr (vsyms, _) (VarExpr var) = 
    (case (vlookup vsyms var) 
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
                                ", " ^ (typestr elstype) ^ ") for then/else"]
                        else T thentype)))
  | checkexpr (decls as (vsyms, fdecls)) (FunCallExpr (fname, fnargs)) = 
    (case flookup fdecls fname 
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
                               else "Non-matching argument types: " ^ 
                                    (typestr ptype) ^ ", " ^ 
                                    (typestr atype) :: (matchargs ps args)
         in
             case matchargs params fnargs
              of [] => T rettype
               | errs => B errs
         end)

(** Type-check single statement, returning list of errors *)
(* Only take most local matching name. If type doesn't match, then error. *)
(* vsyms has both local and global symbols *)
fun checkstmt (vsyms: symtable) adecls fdecls (AssignStmt (var, expr)) = (
  case vlookup vsyms var 
   of SOME vtype => ( 
       case checkexpr (vsyms @ adecls, fdecls) expr of
           B errs => errs
         | T etype => if etype <> vtype 
                      then ["Assignment type mismatch: " ^ (typestr vtype) ^ 
                            ", " ^ (typestr etype)]
                      else [])
    | NONE => (case vlookup adecls var
                of NONE => ["Assignment to undefined variable: " ^ var]
                 | SOME atype => ["Assignment to argument " ^
                                  var ^ " not allowed"]))
  | checkstmt vsyms adecls fdecls (IfStmt (cond, thenblock, elsblock)) = (
    case checkexpr (vsyms @ adecls, fdecls) cond of
        B errs => errs
        (* Inner block: outer variables become 'globals' *)
      | T FmBool => (checkblock vsyms adecls fdecls thenblock) @
                    (case elsblock of SOME sblock => 
                                      checkblock vsyms adecls fdecls sblock
                                      | NONE => []) 
      | T _  => ["Non-Boolean condition in if statement"])
  | checkstmt vsyms argsyms fdecls (WhileStmt (cond, thenblock)) = (
        case checkexpr (vsyms @ argsyms, fdecls) cond of
        B errs => errs
        (* Inner block: outer variables become 'globals' *)
      | T FmBool => (checkblock vsyms argsyms fdecls thenblock)
      | T _  => ["Non-Boolean condition in while statement"])
  | checkstmt vsyms argsyms fdecls (PrintStmt expr) = (
      case checkexpr (vsyms @ argsyms, fdecls) expr of
          B errs => errs
        | T _ => [] )  (* TODO: printable types, from a tenv? *)
  | checkstmt vsyms argsyms fdecls (CallStmt call) = (
      case checkexpr (vsyms @ argsyms, fdecls) (FunCallExpr call) of
          B errs => errs
        | T FmUnit => []
        | T rettype => ["Discarding return value of type " ^ (typestr rettype)])
  | checkstmt vsyms argsyms fdecls (ReturnStmt expr) = (
      case checkexpr (vsyms @ argsyms, fdecls) expr of
          B errs => errs
        | T rettype => (case vlookup argsyms "*return*" of (* special entry to args table *)
                            SOME t => if rettype <> t
                                      then ["Return type doesn't match function type: " ^
                                            (typestr rettype) ^ ", " ^ (typestr t)]
                                      else []
                          | NONE => raise Empty (* shouldn't happen *) ))
                                                           
and checkblock (gsyms: symtable) args (fsyms: fdecl list) (lsyms, stmts) =
  List.concat (map (checkstmt (gsyms @ lsyms) args fsyms) stmts)

(** Check if a statement list always returns *)
fun willreturn [] = false
  | willreturn (stmt::stmts) = case stmt of
                                  ReturnStmt _ => true
                                | IfStmt (e, (_, thenblk), SOME (_, elseblk)) =>
                                  willreturn thenblk andalso willreturn elseblk
                                | _ => willreturn stmts
                                                  
(** Check that all variables used in expressions in a statement list are initialized.
  * Return errors plus variables initialized in this block (for if/else) *)
fun checkinit (initedvars: symtable) [] = ([], initedvars)
  | checkinit initedvars (stmt::stmts) =
    let fun usedvars expr = ( (* This could go outside, doesn't close over anything. *)
          case expr of
              ConstExpr _ => []
            | ConstBool _ => []
            | VarExpr vname => [vname]
            | NotExpr e => usedvars e
            | BoolExpr (_, e1, e2) => (usedvars e1) @ (usedvars e2)
            | CompExpr (_, e1, e2) => (usedvars e1) @ (usedvars e2)
            | ArithExpr (_, e1, e2) => (usedvars e1) @ (usedvars e2)
            | IfExpr (e1, e2, e3) => (usedvars e1) @ (usedvars e2) @ (usedvars e3)
            | FunCallExpr (_, elist) => List.concat (map usedvars elist) )
        (* map lookup, filter nones, map to error messages *)
        fun checkvars vlist = (* closes over initedvars *)
          let val lookups = ListPair.zip (vlist, map (vlookup initedvars) vlist)
              val nones = List.mapPartial (fn p => if isSome (#2 p) then NONE
                                                   else SOME (#1 p)) lookups
          in map (fn v => "Variable " ^ v ^ " may be used before initialization") nones
          end
        val (errs, newinits) = (
            case stmt of
                (* We could strip off the types and just use a list of vars. *)
                AssignStmt (v, expr) => (checkvars (usedvars expr), [(v, FmUnit)])
                (* Add variables that were initialized in both branches *)
              | IfStmt (cond, thenblock, SOME elseblock) =>
                let val (thenerrs, theninits) = checkinit initedvars (#2 thenblock)
                    val (elseerrs, elseinits) = checkinit initedvars (#2 elseblock)
                in (checkvars (usedvars cond) @ thenerrs @ elseerrs,
                    intersect_syms theninits elseinits)
                end
              | IfStmt (cond, thenblock, NONE) =>
                let val (thenerrs, _) = checkinit initedvars (#2 thenblock)
                in (checkvars (usedvars cond) @ thenerrs, [])
                end
              | WhileStmt (cond, whileblock) =>
                let val (whileerrs, _) = checkinit initedvars (#2 whileblock)
                in (checkvars (usedvars cond) @ whileerrs, [])
                end
              | PrintStmt expr => (checkvars (usedvars expr), [])
              | CallStmt (_, elist) => (List.concat (map (checkvars o usedvars) elist), [])
              | ReturnStmt expr => (checkvars (usedvars expr), [])
        )
    in
        (* initalized variables accumulate tail-style, errors direct-style *)
        let val (nexterrs, allinits) = checkinit (newinits @ initedvars) stmts
        in
            (errs @ nexterrs, allinits)
        end 
    end

(** Function: Add return type to argument types and call checkblock on the body. *)
fun checkproc gsyms prevfdecls ({fname, argdecls, rettype}, sblock) =
  let val returnerr = if rettype = FmUnit orelse willreturn (#2 sblock) then []
                      else ["Procedure " ^ fname ^ " may not return a value"]
      val errs = checkblock gsyms (("*return*", rettype)::argdecls) prevfdecls sblock
      val initerrs = #1 (checkinit (gsyms @ argdecls) (#2 sblock))
  in if errs @ returnerr @ initerrs = [] then []
     else "*** Errors in procedure " ^ fname ^ ": " :: (errs @ returnerr @ initerrs)
  end

(** Progress thru function definitions, adding to fdecls table *)
fun checkprogram {gdecls, fdefns, main} =
  let fun checkacc [] accdecls =
        (case main of
             SOME mainblock =>
             let val (initerrs, _) = checkinit gdecls (#2 mainblock)
                 val allerrs = (checkblock gdecls [] accdecls mainblock) @ initerrs
             in 
                 if allerrs = [] then []
                 else "*** Errors in main: " :: allerrs
             end 
           | NONE => [])
        | checkacc ((fdefn as (fdecl, fbody)) :: fdefns) accdecls =
          (checkproc gdecls accdecls fdefn) @ (checkacc fdefns (fdecl::accdecls))
  in checkacc fdefns []
  end
