(* Semantic analysis functions, including typechecking *)

open Fmabsyn;

(** Type-checking functions return a type or a list of errors *)
datatype checkExprResult = T of expr (* Stitch 'em like a monad? *)
                         | B of string list * expr (* errors *) 

(* should check decls and types in different fns? *)

(* exception InternalErr of string (* for things that shouldn't happen *) *)

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

(** Assign a type to an expression. Take expr and return expr, msgs pair *)
fun typeexpr (decls: symtable * ftable)
             {etree=ConstInt i, typ=_} : expr * string list =
    ({etree=ConstInt i, typ=FmInt}, [])
  | typeexpr _ {etree=ConstDouble d, typ=_} =
    ({etree=ConstDouble d, typ=FmDouble}, [])
  | typeexpr _ {etree=ConstBool b, typ=_} =
    ({etree=ConstBool b, typ=FmBool}, [])
  | typeexpr (vsyms, _) (e as {etree=VarExpr var, typ=_}) = (
    case (vlookup vsyms var)
     of SOME entry => ({etree=VarExpr var, typ=(#vtype entry)}, [])
     |  NONE => (e, ["Undefined variable: " ^ var]) )
  | typeexpr decls {etree=NotExpr e1, typ=_} = (
      let val (res, msg1) = typeexpr decls e1
          val typ = if #typ res = Untyped orelse #typ res <> FmBool
                    then Untyped else FmBool
          val msgs = (if #typ res <> FmBool
                      then ["Non-boolean type :" ^ (typestr (#typ res))
                            ^ "in 'not' expression"]
                      else [])
                     @ msg1
      in ({etree=NotExpr e1, typ=typ}, msgs)
      end )
  | typeexpr decls {etree=BoolExpr (oper, e1, e2), typ=_} = (
      let val ((res1, msg1),(res2, msg2)) =
              (typeexpr decls e1, typeexpr decls e2)
          val typ = if #typ res1 = Untyped
                       orelse #typ res2 = Untyped
                       orelse #typ res1 <> FmBool
                       orelse #typ res2 <> FmBool
                    then Untyped else FmBool
          val msgs = (if #typ res1 <> FmBool
                      then ["Non-boolean type : (" ^ (typestr (#typ res1))
                            ^ ") in Boolean expression"]
                      else [])
                     @
                     (if #typ res2 <> FmBool
                      then ["Non-boolean type : (" ^ typestr (#typ res2)
                            ^ ") in Boolean expression"]
                      else [])
                     @ msg1 @ msg2
      in ({etree=BoolExpr (oper, e1, e1), typ=typ}, msgs)
      end )
  | typeexpr decls {etree=CompExpr (oper, e1, e2), typ=_} = (
      let val (({etree=_, typ=t1}, msg1), ({etree=_, typ=t2}, msg2)) =
              (typeexpr decls e1, typeexpr decls e2)
          val (typ,newmsg) =
              if t1 = Untyped orelse t2 = Untyped then (Untyped, "")
              else if t1 <> t2
              then (Untyped, "Different types in comparison: ("
                             ^ (typestr t1) ^ ", " ^ (typestr t2) ^ ")")
              else if (oper = Gt orelse oper = Ge orelse oper = Lt
                       orelse oper = Le)
                      andalso (t1 <> FmInt andalso t1 <> FmDouble)
              then (Untyped, "Ordered comparison of non-ordered type: "
                             ^ (typestr t1))
              else (FmBool, "")
      in ({etree=CompExpr (oper, e1, e2), typ=typ}, newmsg::msg1 @ msg2)
      end )
  | typeexpr decls {etree=ArithExpr (oper, e1, e2), typ=_} = (
      let val (({etree=_, typ=t1}, msg1), ({etree=_, typ=t2}, msg2)) =
              (typeexpr decls e1, typeexpr decls e2)
          val (typ,newmsg) =
              if t1 = Untyped orelse t2 = Untyped then (Untyped, "")
              else if t1 <> t2
              then (Untyped, "Incompatible types in arithmetic expr: (" ^ 
                             (typestr t1) ^ ", " ^ (typestr t2) ^ ")")
              else if t1 <> FmInt andalso t1 <> FmDouble
              then (Untyped,
                    "Non-numeric type in expression: " ^ (typestr t1))
              else (t1, "")
      in ({etree=ArithExpr (oper, e1, e2), typ=typ}, newmsg::msg1 @ msg2)
      end )
  | typeexpr decls {etree=IfExpr (ifexp, thenexp, elsexp), typ=_} = (
      let val ({etree=_, typ=iftype}, msg1) = typeexpr decls ifexp
          val ({etree=_, typ=thentype}, msg2) = typeexpr decls thenexp
          val ({etree=_, typ=elstype}, msg3) = typeexpr decls elsexp
          val (typ, newmsg) =
              if iftype = Untyped orelse thentype = Untyped
                      orelse elstype = Untyped
              then (Untyped, "") (* Just pass existing messages *)
              else if iftype <> FmBool
              then (Untyped, "Non-boolean type for test expression: "
                             ^ typestr iftype)
              else if thentype <> elstype (* One-error-at-a-time approach *)
              then (Untyped, "Non-matching types ("
                             ^ (typestr thentype) ^ ", "
                             ^ (typestr elstype) ^ ") for then/else")
              else (thentype, "")
      in
          ({etree = IfExpr (ifexp, thenexp, elsexp), typ=typ},
           newmsg::msg1 @ msg2 @ msg3)
      end )
  | typeexpr (decls as (vsyms, fdecls)) {etree=FunCallExpr (fname, fnargs),
                                         typ=_} = (
      let fun matchargs [] [] = [] 
            | matchargs (p::ps) [] = ["Not enough arguments to " ^ fname]
            | matchargs [] (p::ps) = ["Too many arguments to " ^ fname]
            | matchargs ({name, vtype, sclass}::ps) (arg::args) = 
              case typeexpr decls arg
               of ({etree=_, typ=Untyped}, msgs) =>
                  msgs @ (matchargs ps args) (* Keep going *)
                | ({etree=_, typ=atype}, msgs) => if atype = vtype
                             (* discarding msgs if typechecks *)
                             then matchargs ps args
                             else "Non-matching argument types: "  
                                  ^ (typestr vtype) ^ ", " 
                                  ^ (typestr atype) :: (matchargs ps args)
          val (typ, msgs) =
              case flookup fdecls fname 
               of NONE => (Untyped, ["Unrecognized function name: " ^ fname])
               |  SOME {fname, argdecls, rettype} =>
                  case matchargs argdecls fnargs
                  (* issue: testing success based on no msgs (see above) *)
                   of [] => (rettype, []) 
                    | errs => (Untyped, errs)
      in ({etree=FunCallExpr (fname, fnargs), typ=typ}, msgs)
      end )
                    
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


(** Typecheck single statement, returning list of errors *)
(* Only take most local matching name. If type doesn't match, then error. *)
(* vsyms has both local and global symbols *)
fun checkstmt (vsyms: symtable) adecls fdecls (AssignStmt (var, expr)) = (
    let val (checkedexpr as {etree=_, typ=etype}, msgs) =
            typeexpr (vsyms @ adecls, fdecls) expr
        val errmsg = 
            case vlookup vsyms var 
             of SOME entry => ( 
                 if etype <> (#vtype entry)
                 then "Assignment type mismatch: " ^ (typestr (#vtype entry))
                      ^ ", " ^ (typestr etype)
                 else "" )
              | NONE => (case vlookup adecls var
                          of NONE => "Assignment to undefined variable: "
                                     ^ var
                           | SOME _ => "Assignment to argument "
                                       ^ var ^ " not allowed" )
    in (AssignStmt (var, checkedexpr), errmsg::msgs)
    end )

  | checkstmt vsyms argsyms fdecls (IfStmt (cond, thenblock, elsblock)) = (
      let val (checkedcond as {etree=_, typ=ctype}, msgs1) =
              typeexpr (vsyms @ argsyms, fdecls) cond
          val (checkedthen, msgs2) =
              checkblock vsyms argsyms fdecls thenblock
          val (checkedelse, msgs3) = (
              case elsblock 
               of SOME sblock => (* A very monadic threading operation *)
                  let val (res, msgs) = checkblock vsyms argsyms fdecls sblock
                  in (SOME res, msgs)
                  end               
                | NONE => (elsblock, []) )
          val errmsg = if ctype <> FmBool
                       then "Non-Boolean condition in if statement"
                       else ""
      in (IfStmt (checkedcond, checkedthen, checkedelse),
          errmsg::msgs1 @ msgs2 @ msgs3)
      end )

  | checkstmt vsyms argsyms fdecls (WhileStmt (cond, bblock)) = (
      let val (checkedcond as {etree=_, typ=ctype}, msgs1) =
              typeexpr (vsyms @ argsyms, fdecls) cond
          val (checkedbody, msgs2) = checkblock vsyms argsyms fdecls bblock 
          val errmsg = if ctype <> FmBool
                       then "Non-Boolean condition in while statement: type "
                            ^ (typestr ctype)
                       else ""
      in (WhileStmt (checkedcond, checkedbody), errmsg::msgs1 @ msgs2)
      end )

  | checkstmt vsyms argsyms fdecls (ForStmt (initstmt, cond, updatestmt,
                                             bblock)) = (
      (* If I want to allow new vardecls in the initstmt, change here *)
      let val (checkedinit, msgs1) = checkstmt vsyms argsyms fdecls initstmt
          val (checkedcond as {etree=_, typ=ctype}, msgs2) =
              typeexpr (vsyms @ argsyms, fdecls) cond
          val (checkedupd, msgs3) = checkstmt vsyms argsyms fdecls updatestmt
          val (checkedbody, msgs4) = checkblock vsyms argsyms fdecls bblock 
          val errmsg = if ctype <> FmBool
                       then "Non-Boolean condition in 'for' statement: "
                            ^ (typestr ctype)
                       else ""
      in (ForStmt (checkedinit, checkedcond, checkedupd, checkedbody),
          errmsg::msgs1 @ msgs2 @ msgs3 @ msgs4)
      end )

  | checkstmt vsyms argsyms fdecls (PrintStmt expr) = (
      let val (checkedexpr, msgs) = typeexpr (vsyms @ argsyms, fdecls) expr
      in
          (PrintStmt checkedexpr, msgs)
      end ) (* TODO: printable types, from a tenv? *)

  | checkstmt vsyms argsyms fdecls (CallStmt callexpr) = (
      (* Parser ensures it's a FunCallExpr *)
      let val (checkedexpr as {etree=_, typ=rettype}, msgs) =
              typeexpr (vsyms @ argsyms, fdecls) callexpr
          val errmsg = if rettype <> FmUnit
                       then "Discarded return value of type "
                            ^ (typestr rettype)
                       else ""
      in (CallStmt checkedexpr, errmsg::msgs)
      end )
  | checkstmt vsyms argsyms fdecls (ReturnStmt (SOME expr)) = (
      let val (checkedexpr as {etree=_, typ=rettype}, msgs) =
              typeexpr (vsyms @ argsyms, fdecls) expr
          val errmsg = (
              case vlookup argsyms "*return*" 
                  (* special entry to args table *)
               of SOME entry => 
                  if rettype <> (#vtype entry)
                  then "Returned value type '" ^ (typestr rettype)
                       ^ "' doesn't match function type '"
                       ^ (typestr (#vtype entry)) ^ "'"
                  else ""
                | NONE => raise Empty )(* if happens, bug in symtable code *)
      in (ReturnStmt (SOME checkedexpr), errmsg::msgs)
      end )
  | checkstmt _ argsyms _ (ReturnStmt NONE) = (
    let val errmsg = (
            case vlookup argsyms "*return*" 
             of SOME entry =>
                if (#vtype entry) <> FmUnit
                then "Empty return statement; expected value of type "
                     ^ typestr (#vtype entry)
                else ""
             | NONE => raise Empty )(* if happens, bug in symtable code *)
    in (ReturnStmt NONE, [errmsg])
    end )
  | checkstmt _ _ _ (BreakStmt {pos=p}) = (BreakStmt {pos=p}, [])

(* start here *)
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
            | ConstDouble _ => []
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
              | IfStmt (cond, thenblock, NONE) =>
                (* vars inited in blocks are thrown away. *)
                let val (thenerrs, _) = checkinit initedvars (#2 thenblock)
                in (checkvars initedvars (usedvars cond) @ thenerrs, [])
                end
              | WhileStmt (cond, whileblock) =>
                let val (whileerrs, _) = checkinit initedvars (#2 whileblock)
                in (checkvars initedvars (usedvars cond) @ whileerrs, [])
                end
              | ForStmt (initstmt, cond, updatestmt, forblock) =>
                let val (initerrs, newinit) = checkinit initedvars [initstmt]
                    val conderrs = checkvars newinit (usedvars cond)
                    (* have to use new var *)
                    val (updateerrs, _) = checkinit newinit [updatestmt]
                    val (blockerrs, _) = checkinit newinit (#2 forblock)
                (* vars init'ed in the for loop initializer are kept
                 * --but not the update, it might not happen *)
                in (initerrs @ conderrs @ updateerrs @ blockerrs, newinit)
                end
              | PrintStmt expr => (checkvars initedvars (usedvars expr), [])
              | CallStmt (_, elist) => (
                  List.concat (map (checkvars initedvars o usedvars) elist),
                  [] )
              | ReturnStmt (SOME expr) =>
                (checkvars initedvars (usedvars expr), [])
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
  * body. TODO: return decorated fdecl. *)
fun checkproc gsyms prevfdecls ({fname, argdecls, rettype}, sblock) =
  let val errs (*, newblock *) =
          checkblock
              gsyms
              ({name="*return*", vtype=rettype, sclass=Local}::argdecls)
              prevfdecls sblock
      val returnerr =
          if rettype = FmUnit orelse willreturn (#2 sblock)
          then []
          else ["Procedure " ^ fname ^ " may not return a value"]
      val initerrs = #1 (checkinit (gsyms @ argdecls) (#2 sblock))
      val breakerrs = checkbreak (#2 sblock)
      (* val newproc = ({fname, argdecls, rettype}, newblock *)
  in (* (newproc, *) if errs @ returnerr @ initerrs @ breakerrs = [] then []
     else "*** Errors in procedure " ^ fname
          ^ ": " :: (errs @ returnerr @ initerrs @ breakerrs)
  end

(** Progress thru function definitions, adding to fdecls table *)
fun checkprogram {ddecls, gdecls, fdefns, main} =
  let val predecls = ddecls @ gdecls
      (* accumulates function definitions *)
      fun checkaccum [] (accdecls: ftable) =
        (* last step: no more functions, check the main block if exists *)
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
          (if isSome flookup fdecl accdels
           then ["*** Error: function redeclaration: " ^ (#fname fdecl)]
           else [])
          @ (checkproc predecls accdedcls fdefn)
          @ (checkaccum fdefns (fdecl::accdecls))
  in checkaccum fdefns []
  end
