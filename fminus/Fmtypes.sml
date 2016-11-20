(* Semantic analysis functions, including typechecking *)

open Fmabsyn;

(** Type-checking functions return a type or a list of errors *)
datatype checkResult = T of valtype (* Stitch 'em like a monad? *)
                     | B of string list (* errors *)

(* should check decls and types in different fns? *)


(*** SYMBOL TABLE FUNCTIONS ***)

(** Look up in variable symbol table *)
(* TODO: replace with more efficient structure, using a memoizing 'maker' *)
fun vlookup ([]:symtable) sym = NONE
  | vlookup ((entry as {name, vtype, sclass})::rest) sym = 
    if name = sym then SOME entry
    else vlookup rest sym

(** Look up in function name symbol table *)
fun flookup ([]:ftable) name = NONE
  | flookup ((entry as {fname, argdecls, rettype})::rest) name =
    if name = fname then SOME entry
    else flookup rest name

(** Find intersection of two symbol tables. *)
fun intersect_syms l1 [] = []
  | intersect_syms [] l2 = []
  | intersect_syms ((entry as {name, vtype, sclass})::es) l2 =
    if isSome (vlookup l2 name)
    then entry::(intersect_syms es l2)
    else (intersect_syms es l2)


(*** SEMANTIC CHECKING FUNCTIONS ***)

fun checkexpr (decls: symtable * ftable) (ConstExpr i) = T FmInt
  | checkexpr _ (ConstBool b) = T FmBool
  | checkexpr (vsyms, _) (VarExpr var) = 
    (case (vlookup vsyms var)
      of SOME entry => T (#vtype entry)
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
       | (T t1, T t2) =>
         if t1 <> t2
         then B ["Incompatible types in arithmetic expr: (" ^ 
                 (typestr t1) ^ ", " ^ (typestr t2) ^ ")"]
         else B ["Non-numeric type in expression: " ^ (typestr t1)])
  | checkexpr decls (IfExpr (ifexp, thenexp, elsexp)) = 
    (case checkexpr decls ifexp (* Good candidate for monadization *)
      of B err => B err
      |  T iftype => 
         if iftype <> FmBool 
         then B ["Non-boolean type for test expression: "
                 ^ typestr iftype]
         else (case checkexpr decls thenexp 
                of B err => B err
                 | T thentype => 
                   (case checkexpr decls elsexp
                     of B err => B err
                      | T elstype => 
                        if thentype <> elstype
                        then B ["Non-matching types ("
                                ^ (typestr thentype) ^ ", "
                                ^ (typestr elstype) ^ ") for then/else"]
                        else T thentype)))
  | checkexpr (decls as (vsyms, fdecls)) (FunCallExpr (fname, fnargs)) = 
    (case flookup fdecls fname 
      of NONE => B ["Unrecognized function name: " ^ fname]
      |  SOME {fname, argdecls, rettype} =>
         (* List of errors in matching, empty if OK *)
         let fun matchargs [] [] = [] 
               | matchargs (p::ps) [] = ["Not enough arguments to " ^ fname]
               | matchargs [] (p::ps) = ["Too many arguments to " ^ fname]
               | matchargs ({name, vtype, sclass}::ps) (arg::args) = 
                 case checkexpr decls arg
                  of B errs => errs @ (matchargs ps args) (* Keep going *)
                  | T atype => if atype = vtype
                               then matchargs ps args
                               else "Non-matching argument types: " ^ 
                                    (typestr vtype) ^ ", " ^ 
                                    (typestr atype) :: (matchargs ps args)
         in
             case matchargs argdecls fnargs
              of [] => T rettype
               | errs => B errs
         end)

                    
(** Check that all statements in a list are reachable. *) 
fun checkreachable [] = []
  | checkreachable (stmt::[]) = [] 
  | checkreachable (stmt1::stmt2::stmts) =
    case stmt1 of
        ReturnStmt _ => ["Unreachable code after return"]
      | BreakStmt {pos} => ["Line " ^ Int.toString pos
                          ^ ": Unreachable code after break"] 
      | _ => checkreachable (stmt2::stmts)

(** Check that a break is inside a loop *)
fun checkbreak [] = []
  | checkbreak (stmt::stmts) =
    case stmt of
        BreakStmt {pos} => ["Line " ^ Int.toString pos
                            ^ ": Break statement used outside of loop"]
      | IfStmt (_, (_, thenstmts), SOME (_, elsestmts)) =>
        (checkbreak thenstmts)
        @ (checkbreak elsestmts)
        @ (checkbreak stmts)
      | IfStmt (_, (_, thenstmts), NONE) =>
        (checkbreak thenstmts) @ (checkbreak stmts)
      | _ => checkbreak stmts
                  
        
(** Type-check single statement, returning list of errors *)
(* Only take most local matching name. If type doesn't match, then error. *)
(* vsyms has both local and global symbols *)
fun checkstmt (vsyms: symtable) adecls fdecls (AssignStmt (var, expr)) = (
  case vlookup vsyms var 
   of SOME entry => ( 
       case checkexpr (vsyms @ adecls, fdecls) expr of
           B errs => errs
         | T etype => if etype <> (#vtype entry)
                      then ["Assignment type mismatch: "
                            ^ (typestr (#vtype entry)) ^ 
                            ", " ^ (typestr etype)]
                      else [])
    | NONE => (case vlookup adecls var
                of NONE => ["Assignment to undefined variable: " ^ var]
                 | SOME _ => ["Assignment to argument " ^
                              var ^ " not allowed"]))
  | checkstmt vsyms adecls fdecls (IfStmt (cond, thenblock,
                                           elsblock)) = (
    case checkexpr (vsyms @ adecls, fdecls) cond of
        B errs => errs
        (* Inner block: outer variables become 'globals' *)
      | T FmBool => (checkblock vsyms adecls fdecls thenblock) @
                    (case elsblock of SOME sblock => 
                                      checkblock vsyms adecls fdecls sblock
                                      | NONE => []) 
      | T _  => ["Non-Boolean condition in if statement"])
  | checkstmt vsyms argsyms fdecls (WhileStmt (cond, thenblock)) = (
        (case checkexpr (vsyms @ argsyms, fdecls) cond of
             B errs => errs
           (* Inner block: outer variables become 'globals' *)
           | T FmBool => []
           | T t  => ["Non-Boolean condition in while statement"
                      ^ (typestr t)])
        @ checkblock vsyms argsyms fdecls thenblock )

  | checkstmt vsyms argsyms fdecls (ForStmt (initstmt, cond, updatestmt,
                                             sblock)) = (
      checkstmt vsyms argsyms fdecls initstmt
      @ (case checkexpr (vsyms @ argsyms, fdecls) cond of
             B errs => errs
           | T FmBool => []
           | T t => ["Non-Boolean condition in 'for' statement: "
                     ^ (typestr t)]) 
      @ checkstmt vsyms argsyms fdecls updatestmt
      @ checkblock vsyms argsyms fdecls sblock )

  | checkstmt vsyms argsyms fdecls (PrintStmt expr) = (
      case checkexpr (vsyms @ argsyms, fdecls) expr of
          B errs => errs
        | T _ => [] )  (* TODO: printable types, from a tenv? *)

  | checkstmt vsyms argsyms fdecls (CallStmt call) = (
      case checkexpr (vsyms @ argsyms, fdecls) (FunCallExpr call) of
          B errs => errs
        | T FmUnit => []
        | T rettype => ["Discarding return value of type "
                        ^ (typestr rettype)])

  | checkstmt vsyms argsyms fdecls (ReturnStmt (SOME expr)) = (
      case checkexpr (vsyms @ argsyms, fdecls) expr of
          B errs => errs
        | T rettype =>
          (case vlookup argsyms "*return*" of
               (* special entry to args table *)
               SOME entry => (* (t, _) => *)
               if rettype <> (#vtype entry)
               then ["Return type '" ^ (typestr rettype)
                     ^ "' doesn't match function type '"
                     ^ (typestr (#vtype entry)) ^ "'"]
               else []
             | NONE => raise Empty (* shouldn't happen *) ))
  | checkstmt _ _ _ (ReturnStmt NONE) = []
  | checkstmt _ _ _ (BreakStmt {pos}) = []
    
and checkblock (gsyms: symtable) args (fsyms: ftable) (lsyms, stmts) =
    List.concat (map (checkstmt (gsyms @ lsyms) args fsyms) stmts)
    @
    checkreachable stmts

(** Check that all variables used in expressions in a statement list are
  * initialized.
  * Return errors plus variables initialized in this block (for if/else) *)
fun checkinit (initedvars: symtable) [] = ([], initedvars)
  | checkinit initedvars (stmt::stmts) =
    (* This could go outside, doesn't close over anything. *)
    let fun usedvars expr = ( 
          case expr of
              ConstExpr _ => []
            | ConstBool _ => []
            | VarExpr vname => [vname]
            | NotExpr e => usedvars e
            | BoolExpr (_, e1, e2) => (usedvars e1) @ (usedvars e2)
            | CompExpr (_, e1, e2) => (usedvars e1) @ (usedvars e2)
            | ArithExpr (_, e1, e2) => (usedvars e1) @ (usedvars e2)
            | IfExpr (e1, e2, e3) => (usedvars e1) @ (usedvars e2)
                                     @ (usedvars e3)
            | FunCallExpr (_, elist) =>
              List.concat (map usedvars elist) )
        (* map lookup, filter nones, map to error messages *)
        fun checkvars ivars vlist =
          (* closes over initedvars - no, for loop needs to add new. *)
          let val lookups = ListPair.zip (vlist, map (vlookup ivars) vlist)
              val nones =
                  List.mapPartial (fn p => if isSome (#2 p) then NONE
                                           else SOME (#1 p)) lookups
          in map (fn v => "Variable '" ^ v
                          ^ "' may be used before initialization") nones
          end
        val (errs, newinits) = (
            case stmt of
                (* We could strip off types and just use a list of vars. *)
                (* ** Assignment initializes. ** *)
                AssignStmt (v, expr) => (* storage class doesn't matter. *)
                 ( checkvars initedvars (usedvars expr),
                   [{name=v, vtype=FmUnit, sclass=Local}] )
                (* Add variables that were initialized in both branches *)
              | IfStmt (cond, thenblock, SOME elseblock) =>
                let val (thenerrs, theninits) =
                        checkinit initedvars (#2 thenblock)
                    val (elseerrs, elseinits) =
                        checkinit initedvars (#2 elseblock)
                in (checkvars initedvars (usedvars cond) @ thenerrs
                    @ elseerrs,
                    intersect_syms theninits elseinits)
                end
              | IfStmt (cond, thenblock, NONE) => (* vars inited in blocks are thrown away. *)
                let val (thenerrs, _) = checkinit initedvars (#2 thenblock)
                in (checkvars initedvars (usedvars cond) @ thenerrs, [])
                end
              | WhileStmt (cond, whileblock) =>
                let val (whileerrs, _) = checkinit initedvars (#2 whileblock)
                in (checkvars initedvars (usedvars cond) @ whileerrs, [])
                end
              | ForStmt (initstmt, cond, updatestmt, forblock) =>
                let val (initerrs, newinit) = checkinit initedvars [initstmt]
                    val conderrs = checkvars newinit (usedvars cond) (* have to use new var *)
                    val (updateerrs, _) = checkinit newinit [updatestmt]
                    val (blockerrs, _) = checkinit newinit (#2 forblock)
                (* vars init'ed in the for loop initializer are kept
                 * --but not the update, it might not happen *)
                in (initerrs @ conderrs @ updateerrs @ blockerrs, newinit)
                end
              | PrintStmt expr => (checkvars initedvars (usedvars expr), [])
              | CallStmt (_, elist) => (
                  List.concat (map (checkvars initedvars o usedvars) elist), [] )
              | ReturnStmt (SOME expr) => (checkvars initedvars (usedvars expr), [])
              | ReturnStmt NONE => ([], [])
              | BreakStmt {pos} => ([], [])
        )
    in
        (* initalized variables accumulate tail-style, errors direct-style *)
        let val (nexterrs, allinits) = checkinit (newinits @ initedvars) stmts
        in
            (errs @ nexterrs, allinits)
        end
    end

(** Check if a statement list always returns *)
fun willreturn [] = false
  | willreturn (stmt::stmts) =
    case stmt of
        ReturnStmt _ => true
      | IfStmt (e, (_, thenblk), SOME (_, elseblk)) =>
        willreturn thenblk andalso willreturn elseblk
      | _ => willreturn stmts

(** Procs: Add return type to argument types and call checkblock on the 
  * body. *)
fun checkproc gsyms prevfdecls ({fname, argdecls, rettype}, sblock) =
  let val errs = checkblock
                     gsyms
                     ({name="*return*", vtype=rettype, sclass=Local}::argdecls)
                     prevfdecls sblock
      val returnerr =
          if rettype = FmUnit orelse willreturn (#2 sblock)
          then []
          else ["Procedure " ^ fname ^ " may not return a value"]
      val initerrs = #1 (checkinit (gsyms @ argdecls) (#2 sblock))
      val breakerrs = checkbreak (#2 sblock)
  in if errs @ returnerr @ initerrs @ breakerrs = [] then []
     else "*** Errors in procedure " ^ fname
          ^ ": " :: (errs @ returnerr @ initerrs @ breakerrs)
  end

(** Progress thru function definitions, adding to fdecls table *)
fun checkprogram {ddecls, gdecls, fdefns, main} =
  let val predecls = ddecls @ gdecls
      fun checkaccum [] accdecls =
        (* at the end, check the main block *)
        (case main of
             SOME mainblock => 
             let val (initerrs, _) = checkinit predecls (#2 mainblock)
                 val allerrs = (checkblock predecls [] accdecls mainblock)
                               @ initerrs
             in 
                 if allerrs = [] then []
                 else "*** Errors in main: " :: allerrs
             end 
           | NONE => [])
        | checkaccum ((fdefn as (fdecl, fbody)) :: fdefns) accdecls =
          (checkproc predecls accdecls fdefn)
          @ (checkaccum fdefns (fdecl::accdecls))
  in checkaccum fdefns []
  end
