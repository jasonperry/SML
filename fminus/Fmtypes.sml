(* Semantic analysis functions, including typechecking *)

open Fmabsyn; (* Symtable functions now there *)

(** Type-checking functions return a type or a list of errors *)
datatype checkExprResult = T of expr (* Stitch 'em like a monad? *)
                         | B of string list * expr (* errors *) 

(* should check decls and types in different fns? *)

(* exception InternalErr of string (* for things that shouldn't happen *) *)

(** Assign a type to an expression. Take expr and return (expr, msgs) *)
fun typeexpr (decls: symtable * ftable)
             {etree=ConstInt i, typ=_, pos} : expr * errormsg list =
    ({etree=ConstInt i, typ=FmInt, pos=pos}, [])
  | typeexpr _ {etree=ConstDouble d, typ=_, pos} =
    ({etree=ConstDouble d, typ=FmDouble, pos=pos}, [])
  | typeexpr _ {etree=ConstBool b, typ=_, pos} =
    ({etree=ConstBool b, typ=FmBool, pos=pos}, [])
  | typeexpr (vsyms, _) (e as {etree=VarExpr var, typ=_, pos}) = (
    case (vlookup vsyms var)
     of SOME entry => ({etree=VarExpr var, typ=(#vtype entry), pos=pos}, [])
     |  NONE => (e, [("Undefined variable: " ^ var, pos)]) )
  | typeexpr decls {etree=NotExpr e1, typ=_, pos} = (
      let val (res, msg1) = typeexpr decls e1
          val typ = if #typ res = Untyped orelse #typ res <> FmBool
                    then Untyped else FmBool
          val msgs = (if #typ res <> FmBool
                      then [("Non-boolean type :" ^ (typestr (#typ res))
                            ^ "in 'not' expression", pos)]
                      else [])
                     @ msg1
      in ({etree=NotExpr e1, typ=typ, pos=pos}, msgs)
      end )
  | typeexpr decls {etree=BoolExpr (oper, e1, e2), typ=_, pos} = (
      let val ((res1, msg1),(res2, msg2)) =
              (typeexpr decls e1, typeexpr decls e2)
          val typ = if #typ res1 = Untyped
                       orelse #typ res2 = Untyped
                       orelse #typ res1 <> FmBool
                       orelse #typ res2 <> FmBool
                    then Untyped else FmBool
          val msgs = (if #typ res1 <> FmBool
                      then [("Non-boolean type : (" ^ (typestr (#typ res1))
                            ^ ") in Boolean expression", pos)]
                      else [])
                     @
                     (if #typ res2 <> FmBool
                      then [("Non-boolean type : (" ^ typestr (#typ res2)
                            ^ ") in Boolean expression", pos)]
                      else [])
                     @ msg1 @ msg2
      in ({etree=BoolExpr (oper, e1, e1), typ=typ, pos=pos}, msgs)
      end )
  | typeexpr decls {etree=CompExpr (oper, e1, e2), typ=_, pos} = (
      let val (({etree=_, typ=t1, pos=pos1}, msg1),
               ({etree=_, typ=t2, pos=pos2}, msg2)) =
              (typeexpr decls e1, typeexpr decls e2)
          val (typ,newmsgs) =
              if t1 = Untyped orelse t2 = Untyped then (Untyped, [])
              else if t1 <> t2
              then (Untyped, [("Different types in comparison: ("
                               ^ (typestr t1) ^ ", " ^ (typestr t2) ^ ")", pos)])
              else if (oper = Gt orelse oper = Ge orelse oper = Lt
                       orelse oper = Le)
                      andalso (t1 <> FmInt andalso t1 <> FmDouble)
              then (Untyped, [("Ordered comparison of non-ordered type: "
                             ^ (typestr t1), pos)])
              else (FmBool, [])
      in ({etree=CompExpr (oper, e1, e2), typ=typ, pos=pos},
          newmsgs @ msg1 @ msg2)
      end )
  | typeexpr decls {etree=ArithExpr (oper, e1, e2), typ=_, pos} = (
      let val (({etree=_, typ=t1, pos=pos1}, msg1),
               ({etree=_, typ=t2, pos=pos2}, msg2)) =
              (typeexpr decls e1, typeexpr decls e2)
          val (typ,newmsgs) =
              if t1 = Untyped orelse t2 = Untyped then (Untyped, [])
              else if t1 <> t2
              then (Untyped, [("Incompatible types in arithmetic expr: (" ^ 
                               (typestr t1) ^ ", " ^ (typestr t2) ^ ")", pos)])
              else if t1 <> FmInt andalso t1 <> FmDouble
              then (Untyped,
                    [("Non-numeric type in expression: " ^ (typestr t1), pos)])
              else (t1, [])
      in ({etree=ArithExpr (oper, e1, e2), typ=typ, pos=pos},
          newmsgs @ msg1 @ msg2)
      end )
  | typeexpr decls {etree=IfExpr (ifexp, thenexp, elsexp), typ=_, pos} = (
      let val ({etree=_, typ=iftype, pos=pos1}, msg1) = typeexpr decls ifexp
          val ({etree=_, typ=thentype, pos=pos2}, msg2) = typeexpr decls thenexp
          val ({etree=_, typ=elstype, pos=pos3}, msg3) = typeexpr decls elsexp
          val (typ, newmsgs) =
              if iftype = Untyped orelse thentype = Untyped
                      orelse elstype = Untyped
              then (Untyped, []) (* Just pass existing messages *)
              else if iftype <> FmBool
              then (Untyped, [("Non-boolean type for test expression: "
                              ^ typestr iftype, pos)])
              else if thentype <> elstype (* One-error-at-a-time approach *)
              then (Untyped, [("Non-matching types ("
                              ^ (typestr thentype) ^ ", "
                              ^ (typestr elstype) ^ ") for then/else", pos)])
              else (thentype, [])
      in
          ({etree = IfExpr (ifexp, thenexp, elsexp), typ=typ, pos=pos},
           newmsgs @ msg1 @ msg2 @ msg3)
      end )
  | typeexpr (decls as (vsyms, fdecls)) {etree=FunCallExpr (fname, fnargs),
                                         typ=_, pos} = (
      let fun matchargs [] [] = [] 
            | matchargs (p::ps) [] = [("Not enough arguments to " ^ fname, pos)]
            | matchargs [] (p::ps) = [("Too many arguments to " ^ fname, pos)]
            | matchargs ({name, vtype, sclass}::ps) (arg::args) = 
              case typeexpr decls arg
               of ({etree=_, typ=Untyped, pos=apos}, msgs) =>
                  msgs @ (matchargs ps args) (* Keep going *)
                | ({etree=_, typ=atype, pos=apos}, msgs) => if atype = vtype
                             (* discarding msgs if typechecks *)
                             then matchargs ps args
                             else ("Non-matching argument types: "  
                                   ^ (typestr vtype) ^ ", " 
                                   ^ (typestr atype), pos) :: (matchargs ps args)
          val (typ, msgs) =
              case flookup fdecls fname 
               of NONE => (Untyped, [("Unrecognized function name: "
                                      ^ fname, pos)])
               |  SOME {fname, argdecls, rettype, pos} =>
                  case matchargs argdecls fnargs
                  (* issue: testing success based on no msgs (see above) *)
                   of [] => (rettype, []) 
                    | errs => (Untyped, errs)
      in ({etree=FunCallExpr (fname, fnargs), typ=typ, pos=pos}, msgs)
      end )

(** Check that all statements in a list are reachable. *) 
fun checkreachable ([]: stmt list) = []
  | checkreachable (stmt::[]) = [] 
  | checkreachable ({stree, pos}::stmt2::stmts) =
    case stree of
        ReturnStmt _ => [("Unreachable code after return", pos)]
      | BreakStmt => [("Unreachable code after break", pos)] 
      | _ => checkreachable (stmt2::stmts)

(** Check that a break is inside a loop *)
fun checkbreak [] = []
  | checkbreak ({stree, pos}::stmts) =
    case stree of
        BreakStmt => [("Break statement used outside of loop", pos)]
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
fun checkstmt (vsyms: symtable) adecls fdecls
              {stree=AssignStmt (var, expr), pos} = (
    let val (checkedexpr as {etree=_, typ=etype, pos=pos1}, msgs) =
            typeexpr (vsyms @ adecls, fdecls) expr
        val newerrs = 
            case vlookup vsyms var 
             of SOME entry => ( 
                 if etype <> (#vtype entry)
                 then [("Assignment type mismatch: " ^ (typestr (#vtype entry))
                        ^ ", " ^ (typestr etype), pos)]
                 else (* if (#sclass entry) = Const error *)[] )
              | NONE => (case vlookup adecls var
                          of NONE => [("Assignment to undefined variable: "
                                       ^ var, pos)]
                           | SOME _ => [("Assignment to argument "
                                         ^ var ^ " not allowed", pos)] )
    in ({stree=AssignStmt (var, checkedexpr), pos=pos}, newerrs @ msgs)
    end )

  | checkstmt vsyms argsyms fdecls 
              {stree=IfStmt (cond, thenblock, elsblock), pos} = (
      let val (checkedcond as {etree=_, typ=ctype, pos=pos1}, msgs1) =
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
          val newerrs = if ctype <> FmBool
                       then [("Non-Boolean condition in if statement", pos)]
                       else []
      in ({stree=IfStmt (checkedcond, checkedthen, checkedelse), pos=pos},
          newerrs @ msgs1 @ msgs2 @ msgs3)
      end )

  | checkstmt vsyms argsyms fdecls
              {stree=WhileStmt (cond, bblock), pos} = (
      let val (checkedcond as {etree=_, typ=ctype, pos=pos1}, msgs1) =
              typeexpr (vsyms @ argsyms, fdecls) cond
          val (checkedbody, msgs2) = checkblock vsyms argsyms fdecls bblock 
          val newerrs = if ctype <> FmBool
                       then [("Non-Boolean condition in while statement: type "
                              ^ (typestr ctype), pos)]
                       else []
      in ({stree=WhileStmt (checkedcond, checkedbody), pos=pos},
          newerrs @ msgs1 @ msgs2)
      end )

  | checkstmt vsyms argsyms fdecls
              {stree=ForStmt (initstmt, cond, updatestmt, bblock), pos} = (
      (* If I want to allow new vardecls in the initstmt, change here *)
      let val (checkedinit, msgs1) = checkstmt vsyms argsyms fdecls initstmt
          val (checkedcond as {etree=_, typ=ctype, pos=cpos}, msgs2) =
              typeexpr (vsyms @ argsyms, fdecls) cond
          val (checkedupd, msgs3) = checkstmt vsyms argsyms fdecls updatestmt
          val (checkedbody, msgs4) = checkblock vsyms argsyms fdecls bblock 
          val newerrs = if ctype <> FmBool
                       then [("Non-Boolean condition in 'for' statement: "
                              ^ (typestr ctype), pos)]
                       else []
      in ({stree=ForStmt (checkedinit, checkedcond, checkedupd, checkedbody),
           pos=pos}, newerrs @ msgs1 @ msgs2 @ msgs3 @ msgs4)
      end )

  | checkstmt vsyms argsyms fdecls
              {stree=PrintStmt expr, pos} = (
      let val (checkedexpr, msgs) = typeexpr (vsyms @ argsyms, fdecls) expr
      in
          ({stree=PrintStmt checkedexpr, pos=pos}, msgs)
      end ) (* TODO: printable types, from a tenv? *)

  | checkstmt vsyms argsyms fdecls
              {stree=CallStmt callexpr, pos} = (
      (* Parser ensures it's a FunCallExpr *)
      let val (checkedexpr as {etree=_, typ=rettype, pos=cpos}, msgs) =
              typeexpr (vsyms @ argsyms, fdecls) callexpr
          val newerrs = if rettype <> FmUnit
                       then [("Discarded return value of type "
                              ^ (typestr rettype), pos)]
                       else []
      in ({stree=CallStmt checkedexpr, pos=pos}, newerrs @ msgs)
      end )
  | checkstmt vsyms argsyms fdecls
              {stree=ReturnStmt (SOME expr), pos} = (
      let val (checkedexpr as {etree=_, typ=rettype, pos=rpos}, msgs) =
              typeexpr (vsyms @ argsyms, fdecls) expr
          val newerrs = (
              case vlookup argsyms "*return*" 
                  (* special entry to args table *)
               of SOME entry => 
                  if rettype <> (#vtype entry)
                  then [("Returned value type '" ^ (typestr rettype)
                         ^ "' doesn't match function type '"
                         ^ (typestr (#vtype entry)) ^ "'", pos)]
                  else []
                (* if happens, bug in symtable code *)
                | NONE => (print "Return not found\n"; raise Empty) )
                            
      in ({stree=ReturnStmt (SOME checkedexpr), pos=pos}, newerrs @ msgs)
      end )
  | checkstmt _ argsyms _ {stree=ReturnStmt NONE, pos} = (
    let val newerrs = (
            case vlookup argsyms "*return*" 
             of SOME entry =>
                if (#vtype entry) <> FmUnit
                then [("Empty return statement; expected value of type "
                       ^ typestr (#vtype entry), pos)]
                else []
              | NONE => (print "Couldn't find return entry\n";
                         raise Empty) )(* if happens, bug in symtable code *)
    in ({stree=ReturnStmt NONE, pos=pos}, newerrs)
    end )
  | checkstmt _ _ _ ({stree=BreakStmt, pos}) =
    ({stree=BreakStmt, pos=pos}, [])

(** Merge global and local symbols to check each statement in a block,
  * then check that every statement is reachable. *)
and checkblock (gsyms: symtable) args (fsyms: ftable) (lsyms, stmts) =
    let val (checkedstmts, msglists) =
            ListPair.unzip (map (checkstmt (gsyms @ lsyms) args fsyms) stmts)
        val msgs = (List.concat msglists) @ checkreachable stmts
    in ((lsyms, checkedstmts), msgs)
    end 

(** Check that all variables used in expressions in a statement list are
  * initialized.
  * Return errors plus variables initialized in this block (for if/else) *)
fun checkinit (initedvars: symtable) [] = ([], initedvars)
  | checkinit initedvars (stmt::stmts) =
    (* This could go outside, doesn't close over anything. *)
    let fun usedvars expr = (
          case (#etree expr) of
              ConstInt _ => []
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
        (** Lookup each variable in the list of inited ones.
          * Keep the ones that aren't initialized. *)
        fun checkvars ivars vlist =
          (* closes over initedvars - no, for loop needs to add new. *)
          let val lookups = ListPair.zip (vlist, map (vlookup ivars) vlist)
              val nones =
                  List.mapPartial (fn p => if isSome (#2 p) then NONE
                                           else SOME (#1 p)) lookups
          in map (fn v => ("Variable '" ^ v
                           ^ "' may be used before initialization",
                           (#pos stmt))) nones
          end
        val (errs, newinits) = (
            case (#stree stmt) of
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
                in (checkvars initedvars (usedvars cond) @ thenerrs,
                    [])
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
              | PrintStmt expr =>
                (checkvars initedvars (usedvars expr), [])
              | CallStmt {etree=FunCallExpr (fname, argexps), typ=_, pos} =>
                (List.concat (map (checkvars initedvars o usedvars) argexps),
                 [])
              | CallStmt _ => raise Empty (* shouldn't happen *) 
              | ReturnStmt (SOME expr) =>
                (checkvars initedvars (usedvars expr), [])
              | ReturnStmt NONE => ([], [])
              | BreakStmt => ([], [])
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
    case (#stree stmt) of
        ReturnStmt _ => true
      | IfStmt (e, (_, thenblk), SOME (_, elseblk)) =>
        willreturn thenblk andalso willreturn elseblk
      | _ => willreturn stmts 

(** Procs: Add return type to argument types and call checkblock on the body *)
fun checkproc gsyms prevfdecls (top as {fname, argdecls, rettype, pos},
                                sblock as (blksyms, stmtlist)) =
  let val (newblock, errs) = 
          checkblock
              gsyms
              (* Add return type to proc's -argument- symbol table *)
              ({name="*return*", vtype=rettype, sclass=Local}::argdecls)
              prevfdecls sblock 
      val returnerr = 
          if rettype = FmUnit orelse willreturn stmtlist
          then []
          else [("Procedure " ^ fname ^ " may not return a value", pos)]
      val initerrs = #1 (checkinit (gsyms @ argdecls) stmtlist)
      val breakerrs = ( print "did checkinit\n"; checkbreak stmtlist )
      val newproc = (top, newblock)
  in (newproc, if errs @ returnerr @ initerrs @ breakerrs = [] then []
               else (*"*** Errors in procedure " ^ fname
                    ^ ": " ::*) (errs @ returnerr @ initerrs @ breakerrs))
  end

(** must get new versions of fdefns and main, plus return errors *)
fun checkprogram {ddecls, gdecls, fdefns, main} =
  let val predecls = ddecls @ gdecls
      (** Accumulates list of checked function definitions and errors *)
      fun checkaccum [] (accdefns: fdefn list) accerrs =
        (accdefns, (* rev *) accerrs) (* don't reverse args IN a function *)
        | checkaccum ((fdefn as (fdecl, fbody)) :: frest) accdefns accerrs = (
            let val accdecls = map #1 accdefns
                val newerrs =
                    if isSome (flookup accdecls (#fname fdecl))
                    then [("*** Error: function redeclaration: "
                           ^ (#fname fdecl), (#pos fdecl))]
                    else []
                val (newfdefn, procerrs) = (checkproc predecls accdecls fdefn)
            in checkaccum frest
                          (newfdefn::accdefns) (* bottom first *)
                          (newerrs @ procerrs @ accerrs) (* reverse at end *)
            end )
      val (newfdefns, errs) = checkaccum fdefns [] []
      val newfdecls = (print "finished checking functions\n"; map #1 newfdefns)
      (* main is treated separately (for now) *)
      val (newmain, mainerrs) =
          case main
           of SOME (mainblock as (mainsyms, mainstmts)) =>
              let val (initerrs, _) = checkinit predecls mainstmts
                  val (newmblock, blkerrs) = 
                      checkblock
                          predecls
                          (* Only argument symbol is return type of Unit *)
                          [{name="*return*", vtype=FmUnit, sclass=Local}]
                          newfdecls mainblock 
                  val mainerrs =
                      if blkerrs @ initerrs <> []
                      then (*"*** Errors in main: " ::*) (blkerrs @ initerrs)
                      else []
              in (SOME newmblock, mainerrs)
              end
            | NONE => (NONE, [])
  in
      ({ddecls=ddecls, gdecls=gdecls, fdefns=newfdefns, main=newmain},
       errs @ mainerrs)
  end
