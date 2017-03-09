(* Semantic analysis functions, including typechecking *)

open Fmabsyn;
open Either;
(* open Symtable; *) (* currently defined at header level *)

(* should check decls and types in different fns? *)

(* exception InternalErr of string (* for things that shouldn't happen *) *)

val debug = true
fun debugPrint s = if debug then
                       TextIO.output (TextIO.stdErr, s)
                   else ()

(** Attempt to reduce an expression to a constval *)
fun evalConstExp syms (e as {etree, typ=_, pos=_}: expr) =
  case etree
   of ConstExpr ce => SOME ce
    | VarExpr v => (
        case Symtable.lookup syms v
         of SOME {sclass=Const, cval=SOME cval, ...} => SOME cval
                (* {name=_, vtype=_, sclass=(Const cval)} => SOME cval *)
          | SOME _ => NONE
          | NONE => NONE (* don't bother throwing error here *) )
    | NotExpr e => (
        case evalConstExp syms e
         of SOME (BoolVal b) => SOME (BoolVal (not b))
          | SOME _ => NONE
          | NONE => NONE )
    | BoolExpr (oper, e1, e2) => ((
        case (oper, valOf (evalConstExp syms e1), valOf (evalConstExp syms e2))
         of (And, BoolVal b1, BoolVal b2) => SOME (BoolVal (b1 andalso b2))
          | (Or, BoolVal b1, BoolVal b2) => SOME (BoolVal (b1 orelse b2))
          | _ => NONE )
                                  handle Option => NONE )
    | CompExpr (oper, e1, e2) => ((
        case (oper, valOf (evalConstExp syms e1), valOf (evalConstExp syms e2))
         of (Eq, IntVal i1, IntVal i2) => SOME (BoolVal (i1 = i2))
          | (Eq, BoolVal b1, BoolVal b2) => SOME (BoolVal (b1 = b2))
          | (Ne, IntVal i1, IntVal i2) => SOME (BoolVal (i1 <> i2))
          | (Ne, BoolVal b1, BoolVal b2) => SOME (BoolVal (b1 <> b2))
          | (Gt, IntVal i1, IntVal i2) => SOME (BoolVal (i1 > i2))
          | (Gt, DoubleVal d1, DoubleVal d2) => SOME (BoolVal (d1 > d2))
          | (Ge, IntVal i1, IntVal i2) => SOME (BoolVal (i1 >= i2))
          | (Ge, DoubleVal d1, DoubleVal d2) => SOME (BoolVal (d1 >= d2))
          | (Lt, IntVal i1, IntVal i2) => SOME (BoolVal (i1 < i2))
          | (Lt, DoubleVal d1, DoubleVal d2) => SOME (BoolVal (d1 < d2))
          | (Le, IntVal i1, IntVal i2) => SOME (BoolVal (i1 <= i2))
          | (Le, DoubleVal d1, DoubleVal d2) => SOME (BoolVal (d1 <= d2))
          | _ => NONE)
                                  handle Option => NONE )
    | ArithExpr (oper, e1, e2) => ((
        case (oper, valOf (evalConstExp syms e1), valOf(evalConstExp syms e2))
         of (Plus, IntVal i1, IntVal i2) => SOME (IntVal (i1 + i2))
          | (Plus, DoubleVal d1, DoubleVal d2) => SOME (DoubleVal (d1 + d2))
          | (Minus, IntVal i1, IntVal i2) => SOME (IntVal (i1 - i2))
          | (Minus, DoubleVal d1, DoubleVal d2) => SOME (DoubleVal (d1 - d2))
          | (Times, IntVal i1, IntVal i2) => SOME (IntVal (i1 * i2))
          | (Times, DoubleVal d1, DoubleVal d2) => SOME (DoubleVal (d1 * d2))
          | (Div, IntVal i1, IntVal i2) => SOME (IntVal (i1 div i2))
          | (Div, DoubleVal d1, DoubleVal d2) => SOME (DoubleVal (d1 / d2))
          | (Mod, IntVal i1, IntVal i2) => SOME (IntVal (i1 mod i2))
            (* watch out for precision loss. MosML defaults to 63 bits *)
          | (Xor, IntVal i1, IntVal i2) =>
            SOME (IntVal (Word.toInt (Word.xorb
                                          (Word.fromInt i1, Word.fromInt i2))))
          | (Bitand, IntVal i1, IntVal i2) =>
            SOME (IntVal (Word.toInt (Word.andb
                                          (Word.fromInt i1, Word.fromInt i2))))
          | (Bitor, IntVal i1, IntVal i2) =>
            SOME (IntVal (Word.toInt (Word.orb
                                          (Word.fromInt i1, Word.fromInt i2))))
          | _ => NONE )
                                   handle Option => NONE )
    | IfExpr (condexp, thenexp, elseexp) => (
        case evalConstExp syms condexp
         of SOME (BoolVal b) => if b then evalConstExp syms thenexp
                                else evalConstExp syms elseexp
          | _ => NONE )
    | FunCallExpr _  => NONE (* If it's pure and the args are constants... *)


(** Assign a type to an expression. Take expr and return (expr, msgs) *)
fun typeexpr (decls: Symtable.symtable * Funtable.symtable)
             {etree=ConstExpr (IntVal i), typ=_, pos} : expr * errormsg list =
    ({etree=ConstExpr (IntVal i), typ=FmInt, pos=pos}, [])
  | typeexpr _ {etree=ConstExpr (DoubleVal d), typ=_, pos} =
    ({etree=ConstExpr (DoubleVal d), typ=FmDouble, pos=pos}, [])
  | typeexpr _ {etree=ConstExpr (BoolVal b), typ=_, pos} =
    ({etree=ConstExpr (BoolVal b), typ=FmBool, pos=pos}, [])
  | typeexpr (vsyms, _) (e as {etree=VarExpr var, typ=_, pos}) = (
    case (Symtable.lookup vsyms var)
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
      let fun matchargs [] [] = [] (* match formal and actual params *)
            | matchargs (p::ps) [] = [("Not enough arguments to " ^ fname, pos)]
            | matchargs [] (p::ps) = [("Too many arguments to " ^ fname, pos)]
            | matchargs ((name, vtype)::ps) (arg::args) = 
              case typeexpr decls arg
               of ({etree=_, typ=Untyped, pos=apos}, msgs) =>
                  msgs @ (matchargs ps args) (* Keep going *)
                | ({etree=_, typ=atype, pos=apos}, msgs) => if atype = vtype
                             (* discarding msgs if typechecks *)
                             then matchargs ps args
                             else ("Non-matching argument types: "  
                                   ^ (typestr vtype) ^ ", " 
                                   ^ (typestr atype), pos)::(matchargs ps args)
          val (typ, msgs) =
              case Funtable.lookup fdecls fname 
               of NONE => (Untyped, [("Unrecognized function name: "
                                      ^ fname, pos)])
               |  SOME {fname, params, rettype, pos} =>
                  case matchargs params fnargs
                  (* issue: testing success based on no msgs (see above) *)
                   of [] => (rettype, []) 
                    | funerrs => (Untyped, funerrs)
      in ({etree=FunCallExpr (fname, fnargs), typ=typ, pos=pos}, msgs)
      end )

(** Helper function for checking conditionals and ensuring they're bools. *)
fun typecond decls expr =
  let val (newexpr, errs) = typeexpr decls expr
  in if #typ newexpr = FmBool then (newexpr, errs)
     else (newexpr, errs @ [("Non-boolean type for condition", #pos newexpr)])
  end
                                                           
(** Add a declaration to a local symtable, or return error *)
fun addDecl (sclass: storeclass) ({name, vtype, pos, dtype}:decl) syms =
  if isSome (Symtable.lookup syms name)
  then ERR ("Redeclaration of " ^ name, pos)
  else (
      case dtype
       of VarDecl =>
          VAL (Symtable.insert syms {name=name, vtype=vtype,
                                     sclass=sclass, cval=NONE})
       | ConstDecl expr => ( (* Const declarations need to be evaluated *)
           case evalConstExp syms expr
            of NONE =>
               ERR ("Non-constant initializer for " ^ name, pos)
             | SOME (IntVal v) => 
               if vtype = FmInt
               then VAL (Symtable.insert syms
                                         {name=name, vtype=vtype,
                                          sclass=Const, cval=SOME (IntVal v)})
               else ERR ("Const initializer type mismatch for " ^ name ^
                         ": declared as " ^ (typestr vtype) ^
                         ", initializer is int", pos)
             | SOME (DoubleVal v) => 
               if vtype = FmDouble
               then VAL (Symtable.insert syms
                                         {name=name, vtype=vtype, sclass=Const,
                                          cval=SOME (DoubleVal v)})
               else ERR ("Const initializer type mismatch for " ^ name ^
                         ": declared as " ^ (typestr vtype) ^
                         ", initializer is double", pos)
             | SOME (BoolVal v) => 
               if vtype = FmBool
               then VAL (Symtable.insert syms
                                         {name=name, vtype=vtype,sclass=Const,
                                          cval=SOME (BoolVal v)})
               else ERR ("Const initializer type mismatch for " ^ name ^
                         ": declared as " ^ (typestr vtype) ^
                         ", initializer is bool", pos))
       | IODecl sclass => VAL (Symtable.insert
                                   syms
                                   {name=name, vtype=vtype,
                                    sclass=sclass, cval=NONE})
  )
                                                           
(** Check that all statements in a list are reachable. *) 
fun checkreachable ([]: stmt list) = []
  | checkreachable (stmt::[]) = [] 
  | checkreachable ({stree, pos}::stmt2::stmts) =
    case stree of
        ReturnStmt _ => [("Unreachable code after return", pos)]
      | BreakStmt => [("Unreachable code after break", pos)] 
      | _ => checkreachable (stmt2::stmts)

(** Check that a break is inside a loop; the bodies of for and while loops
  *  are skipped over, breaks are flagged, and we recurse inside ifs. *)
fun checkbreak [] = []
  | checkbreak ({stree, pos}::stmts) =
    case stree of
        BreakStmt => [("Break statement used outside of loop", pos)]
      | IfStmt (_, (_, thenstmts), eliflist, SOME (_, elsestmts)) =>
        (checkbreak thenstmts)
        @ List.concat (map (fn (_, (_, elifstmt)) => checkbreak elifstmt)
                           eliflist)
        @ (checkbreak elsestmts)
        @ (checkbreak stmts)
      | IfStmt (_, (_, thenstmts), eliflist, NONE) =>
        (checkbreak thenstmts) @ (checkbreak stmts)
      | _ => checkbreak stmts


(** Typecheck single statement, returning new statement, list of errors,
  *  and list of newly-declared symbols for constructing the symtable. 
  * Only take most local matching name. If type doesn't match, then error. *)
fun checkstmt outsyms locsyms fsyms {stree=DeclStmt dlist, pos} =
  let val (newsyms, errs) = foldEither (addDecl Local)
                                       (* Why? Why not empty table? *)
                                       (locsyms: Symtable.symtable)
                                       (dlist: decl list)
  in ({stree=DeclStmt dlist, pos=pos}, errs, newsyms) (* Empty it out? *)
  end
  | checkstmt outsyms locsyms fsyms 
              {stree=AssignStmt (var, expr), pos} = (
    let val (checkedexpr as {etree=_, typ=etype, pos=pos1}, msgs) =
            typeexpr (Symtable.merge locsyms outsyms, fsyms) expr
        val entry = if isSome (Symtable.lookup locsyms var) then
                        Symtable.lookup locsyms var
                    else Symtable.lookup outsyms var
        val newerrs = 
            case entry
             of SOME e => ( 
                 if etype <> (#vtype e) then
                     [("Assignment type mismatch: " ^ (typestr (#vtype e))
                       ^ ", " ^ (typestr etype), pos)]
                 else if (#sclass e) = Const then
                     [("Assignment to const: " ^ var, pos)]
                 else if (#sclass e) = Arg then
                     [("Assignment to argument: " ^ var, pos)] 
                 else [] )
              | NONE => [("Assignment to undefined variable: " ^ var, pos)]
    in ({stree=AssignStmt (var, checkedexpr), pos=pos}, newerrs @ msgs,
        locsyms)
    end )

  | checkstmt outsyms locsyms fsyms 
              {stree=IfStmt (cond, thenblock, elifs, elseblock), pos} = (
      let val varsyms = Symtable.merge locsyms outsyms
          val (checkedcond, conderrs) =
              typecond (varsyms, fsyms) cond
          val (checkedthen, thenerrs) =
              checkblock varsyms fsyms thenblock
          val (checkedelifs, eliferrs) = (* major surgery *)
              let val checkedconds = (* expr * errs list *)
                      map (fn (c, _) => typecond (varsyms, fsyms) c) elifs
                  val checkedblocks = (* sblock * errs list *)
                      map (fn (_, b) => checkblock varsyms fsyms b) elifs
                  val (conds, conderrs) = ListPair.unzip checkedconds
                  val (blocks, blockerrs) = ListPair.unzip checkedblocks
                  (* Intersperse cond errors with their respective blocks. 
                   *  All errors have to be exported to the statement. *)
                  val appderrs =
                      List.concat (ListPair.map op@ (conderrs, blockerrs))
              in (ListPair.zip (conds, blocks), appderrs)
              end
          val (checkedelse, elseerrs) = (
              case elseblock 
               of SOME sblock => 
                  let val (res, msgs) = checkblock varsyms fsyms sblock
                  in (SOME res, msgs)
                  end               
                | NONE => (elseblock, []) )
      in ({stree=IfStmt (checkedcond, checkedthen, checkedelifs, checkedelse),
           pos=pos},
          conderrs @ thenerrs @ eliferrs @ elseerrs,
          locsyms) (* syms in then/elif/else blocks not exported *)
      end )

  | checkstmt outsyms locsyms fsyms
              {stree=WhileStmt (cond, bblock), pos} = (
      let val (checkedcond as {etree=_, typ=ctype, pos=pos1}, msgs1) =
              typeexpr (Symtable.merge locsyms outsyms, fsyms) cond
          val (checkedbody, msgs2) =
              checkblock (Symtable.merge locsyms outsyms) fsyms bblock 
          val newerrs = if ctype <> FmBool
                       then [("Non-Boolean condition in while statement: type "
                              ^ (typestr ctype), pos)]
                       else []
      in ({stree=WhileStmt (checkedcond, checkedbody), pos=pos},
          newerrs @ msgs1 @ msgs2, locsyms)
      end )

  | checkstmt outsyms locsyms fsyms
              {stree=ForStmt (initstmt, cond, updatestmt, bblock), pos} = (
      (* If I want to allow new vardecls in the initstmt, change here *)
      let val (checkedinit, msgs1, locsyms2) = (* new symbols allowed! *)
              checkstmt outsyms locsyms fsyms initstmt
          val (checkedcond as {etree=_, typ=ctype, pos=cpos}, msgs2) =
               typeexpr (Symtable.merge locsyms2 outsyms, fsyms) cond
          val (checkedupd, msgs3, locsyms3) =
              checkstmt outsyms locsyms2 fsyms updatestmt
          val (checkedbody, msgs4) =
              checkblock (Symtable.merge outsyms locsyms3) fsyms bblock 
          val newerrs = if ctype <> FmBool
                       then [("Non-Boolean condition in 'for' statement: "
                              ^ (typestr ctype), pos)]
                       else []
      in ({stree=ForStmt (checkedinit, checkedcond, checkedupd, checkedbody),
           pos=pos}, newerrs @ msgs1 @ msgs2 @ msgs3 @ msgs4,
          locsyms) (* discard locsyms2,3,4 *)
      end )

  | checkstmt outsyms locsyms fsyms
              {stree=PrintStmt expr, pos} = (
      let val (checkedexpr, msgs) =
              typeexpr (Symtable.merge locsyms outsyms, fsyms) expr
      in
          ({stree=PrintStmt checkedexpr, pos=pos}, msgs, locsyms)
      end ) (* TODO: printable types, from a tenv? *)

  | checkstmt outsyms locsyms fsyms
              {stree=CallStmt callexpr, pos} = (
      (* Parser ensures it's a FunCallExpr *)
      let val (checkedexpr as {etree=_, typ=rettype, pos=cpos}, msgs) =
              typeexpr (Symtable.merge locsyms outsyms, fsyms) callexpr
          val newerrs = if rettype <> FmUnit then
                            [("Discarded return value of type "
                              ^ (typestr rettype), pos)]
                       else []
      in ({stree=CallStmt checkedexpr, pos=pos}, newerrs @ msgs, locsyms)
      end )
  | checkstmt outsyms locsyms fsyms
              {stree=ReturnStmt (SOME expr), pos} = (
      let val (checkedexpr as {etree=_, typ=rettype, pos=rpos}, msgs) =
              typeexpr (Symtable.merge locsyms outsyms, fsyms) expr
          val newerrs = (
              let val retentry =
                      if isSome (Symtable.lookup locsyms "*return*") then
                          (Symtable.lookup locsyms "*return*")
                      else Symtable.lookup outsyms "*return*"
              in case retentry (* special entry to table *)
                  of SOME entry => 
                     if rettype <> (#vtype entry)
                     then [("Returned value type : '" ^ (typestr rettype)
                            ^ "' doesn't match function type : '"
                            ^ (typestr (#vtype entry)) ^ "'", pos)]
                     else []
                   (* if happens, bug in symtable code *)
                   | NONE => (print "Return not found\n"; raise Empty) 
              end )
      in ({stree=ReturnStmt (SOME checkedexpr), pos=pos}, newerrs @ msgs,
          locsyms)
      end )
  | checkstmt outsyms locsyms _ {stree=ReturnStmt NONE, pos} = (
      let val newerrs = (
              let val retentry = if isSome (Symtable.lookup locsyms "*return*")
                                 then (Symtable.lookup locsyms "*return*")
                                 else Symtable.lookup outsyms "*return*"
              in case retentry
                  of SOME entry =>
                     if (#vtype entry) <> FmUnit
                     then [("Empty return statement; expected value of type "
                            ^ typestr (#vtype entry), pos)]
                     else []
                   | NONE => (print "Couldn't find return entry\n";
                              raise Empty)
              end )(* means bug in symtable code *)
      in ({stree=ReturnStmt NONE, pos=pos}, newerrs, locsyms)
      end )
  | checkstmt _ locsyms _ ({stree=BreakStmt, pos}) =
    ({stree=BreakStmt, pos=pos}, [], locsyms)


(** Merge global and local symbols to check each statement in a block,
  * then check that every statement is reachable. *)
and checkblock outsyms fsyms ((lsyms, stmts): sblock) =
    (* lsyms should be empty *)
    let fun chkblockacc [] symacc erracc stmtacc =
          (((symacc, rev stmtacc): sblock), erracc)
          | chkblockacc (stmt::rest) symacc erracc stmtacc =
            let val (newstmt, errs, newsyms) =
                    checkstmt outsyms symacc fsyms stmt
            in chkblockacc rest newsyms (erracc @ errs) (newstmt::stmtacc)
                        (* checkstmt folds in newsyms itself. *)
                        (* keep global (outside) syms separate to distinguish
                         * shadowing and redefinition *)
                        (* checkstmt will check if declared before use,
                         * so can keep all syms *)
            end 
        val (newblock, errs) = chkblockacc stmts Symtable.empty [] []
    in 
        (newblock, errs @ (checkreachable stmts))
    end 

fun inlist a [] = false
  | inlist a (b::bs) = if a = b then true else inlist a bs

fun listremove (a, []) = []  (* tupled for std library's foldl *)
  | listremove (a, (b::bs)) = if a = b then listremove (a, bs)
                           else b::(listremove (a, bs))
fun listdiff blist alist = foldl listremove blist alist
fun listintersect [] _ = []
  | listintersect _ [] = []
  | listintersect (a::rest) b =
    if inlist a b then (* get rid of after finding once *)
        a::(listintersect rest (listremove (a, b)))
    else listintersect rest b

(** Find any uninited variables in a block.
  * Propagates a list of unininitialized variables, which are added to at
  * a declaration and removed when one is inited. *)
fun checkinit stmts =
  (* Return a list of variables used in an expression. *)
  let fun usedvars expr = (
          case (#etree expr) of
              ConstExpr _ => []
            | VarExpr vname => [vname]
            | NotExpr e => usedvars e
            | BoolExpr (_, e1, e2) => (usedvars e1) @ (usedvars e2)
            | CompExpr (_, e1, e2) => (usedvars e1) @ (usedvars e2)
            | ArithExpr (_, e1, e2) => (usedvars e1) @ (usedvars e2)
            | IfExpr (e1, e2, e3) => (usedvars e1) @ (usedvars e2)
                                     @ (usedvars e3)
            | FunCallExpr (_, elist) =>
              List.concat (map usedvars elist) )

      (** Look up each variable in a list of uninited ones.
        * Generate error message for each one that's present. *)
      fun checkvars uninited vlist pos =
        let val noninited = List.filter (fn v => inlist v uninited) vlist
        in map (fn v => ("Variable '" ^ v
                         ^ "' may be used before initialization", pos))
               noninited
        end
      (** Return a list of non-local variables initialized in a block.
       *  For seeing if then/else blocks initialize anything. *)
      (* Could I include this in checkinit main function if I add localvars? *)
      fun initexports stmts =
        let fun initexports' localvars [] = []
              | initexports' localvars (stmt::stmts) = (
                  case (#stree stmt)
                   of DeclStmt dlist => (* add to local var list *)
                      initexports' ((map #name dlist) @ localvars) stmts
                    | AssignStmt (vname, _) => (* if not local, add it *)
                      if not (inlist vname localvars)
                      then vname::(initexports' localvars stmts)
                      else initexports' localvars stmts
                    | ForStmt (initstmt, _, _, _) =>
                      (* For loop's initializer can init, block can't *)
                      initexports' localvars (initstmt::stmts)
                    | IfStmt (_, _, _, NONE) => initexports' localvars stmts
                    | IfStmt (_, thenblock, elifs, SOME elseblock) =>
                      (isectexports
                           (#2 thenblock::(map #2 (map #2 elifs)
                                           @ [#2 elseblock]))
                       @ (initexports' localvars stmts))
                    | _ => initexports' localvars stmts )
        in initexports' [] stmts
        end
      (** then- and else- blocks must both initialize a varible for it
        * to count as initialize, so we intersect *)
      and isectexports ([]: stmt list list) = []
        (* Generalizes to multiple if, elsif, else blocks *)
        | isectexports [slist] = initexports slist
        | isectexports (slist::rest) =
          listintersect (initexports slist) (isectexports rest)

      (* main loop, accumulating uninited vars and errs (string * pos) *)
      (* TODO: factor out the concatenation parts? *)
      fun checkinit' [] uninited errs = errs
        | checkinit' (stmt::stmts) uninited errs = (
            case (#stree stmt)
             of DeclStmt dlist => (* declaration adds uninited variables *)
                checkinit' stmts ((map #name dlist) @ uninited) errs
              | AssignStmt (varname, expr) =>
                checkinit' stmts (* assigned var is initialized now *)
                           (listremove (varname, uninited))
                           ((checkvars uninited (usedvars expr) (#pos stmt))
                            @ errs)
              | IfStmt (cond, (_, ifstmts), elifs, NONE) =>
                checkinit' stmts
                           uninited
                           ((checkvars uninited (usedvars cond) (#pos stmt))
                            @ List.concat (map (fn (_, (_, sts)) =>
                                                   checkinit' sts uninited [])
                                               elifs)
                            @ checkinit' ifstmts uninited []
                            @ errs)
              | IfStmt (cond, (_, ifstmts), elifs, SOME (_, elsstmts)) =>
                let val exportedinits = (isectexports (ifstmts::elsstmts::
                                                       (map (#2 o #2) elifs)))
                in 
                    checkinit'
                        stmts (* Remove variables inited in all blocks *)
                        (listdiff uninited exportedinits)
                        ((checkvars uninited (usedvars cond) (#pos stmt))
                         (* pass same uninited *)
                         @ checkinit' elsstmts uninited []
                         @ List.concat (map (fn (_, (_, sts)) =>
                                                checkinit' sts uninited [])
                                            elifs)
                         @ checkinit' ifstmts uninited [] (* upside down *)
                         @ errs)
                end
              | WhileStmt (cond, body) =>
                checkinit' stmts
                           uninited (* body might not run, no inits exported *)
                           ((checkvars uninited (usedvars cond) (#pos stmt))
                            @ (checkinit' (#2 body) uninited [])
                            @ errs)
              | ForStmt ({stree=AssignStmt (varname, initexpr), pos=pos},
                         cond, updstmt, body) =>
                (* The initializer statement exports its init. *)
                let val uninit' = listremove (varname, uninited)
                in
                    checkinit' stmts uninit'
                               (* Update stmt is logically at end of loop *)
                               ((checkinit' ((#2 body) @ [updstmt]) uninit' [])
                                @ (checkvars uninit' (usedvars cond) pos)
                                @ (checkvars uninited (usedvars initexpr) pos)
                                @ errs )
                end
              | ForStmt (_, _, _, _) => raise Empty (* must be AssignStmt *)
              | PrintStmt expr => 
                checkinit' stmts uninited
                           ((checkvars uninited (usedvars expr) (#pos stmt))
                            @ errs)
              | CallStmt expr =>
                checkinit' stmts uninited
                           ((checkvars uninited (usedvars expr) (#pos stmt))
                            @ errs)
              | ReturnStmt NONE => checkinit' stmts uninited errs
              | ReturnStmt (SOME expr) =>
                checkinit' stmts uninited
                           ((checkvars uninited (usedvars expr) (#pos stmt))
                            @ errs)
              | BreakStmt => checkinit' stmts uninited errs
        )
  in rev (checkinit' stmts [] [])
  end 


(** Check if a statement list always returns *)
fun willreturn [] = false
  | willreturn (stmt::stmts) = 
    case (#stree stmt) of
        ReturnStmt _ => true
      | IfStmt (e, (_, thensts), elifs, SOME (_, elsests)) =>
        let val elifsblocks = map (#2 o #2) elifs
        in (List.all willreturn (thensts::elsests::elifsblocks))
           orelse willreturn stmts
        end 
      | _ => willreturn stmts 

(** Add params to a symtable *)
fun addparams syms [] = syms
  | addparams syms ((name, vtype)::rest) =
    Symtable.insert (addparams syms rest)
                    ({name=name, vtype=vtype, sclass=Arg, cval=NONE})

(** Procs: Add return type to argument types and call checkblock on the body *)
fun checkproc gsyms prevfsyms (header as {fname, params, rettype, pos},
                               sblock (* as (blksyms, stmtlist)*)) =
  (* Formerly: add return type to proc's parameter symtable *)
  (* Now add params and return type to outer syms *)
  let val procsyms = Symtable.insert (addparams gsyms params)
                                     {name="*return*", vtype=rettype,
                                      sclass=Local, cval=NONE}
      val _ = debugPrint ("Proc symtable: " ^ Symtable.toString procsyms)
      val (newblock, funerrs) = checkblock procsyms prevfsyms sblock
      (* Additional non-modifying analyses: return, break, inited variables.
       *  They don't return new structures. *)
      val returnerr = 
          if rettype = FmUnit orelse willreturn (#2 sblock) (* stmtlist *)
          then []
          else [("Procedure " ^ fname ^ " may not return a value", pos)]
      (* Don't have to pass any syms to check uninited *)
      val initerrs = checkinit (#2 sblock)
      val breakerrs = checkbreak (#2 sblock)
      val newproc = (header, newblock)
  in (newproc, if funerrs @ returnerr @ initerrs @ breakerrs = [] then []
               else (*"*** Errors in procedure " ^ fname ^ ": " ::*)
                   (funerrs @ returnerr @ initerrs @ breakerrs))
  end

(** must get new versions of fdefns and main, plus return errors *)
fun checkprogram (PGM {iodecls, gdecls, fdefns, gsyms, fsyms, main}) =
  (* raise if symtables not empty? *)
  let val (newgsyms, gdeclerrs) =
          (* addDecl ignores the 'Global' for the iodecl type *)
          foldEither (addDecl Global) Symtable.empty (iodecls @ gdecls)
      (** Accumulates list of checked function definitions and errors *)
      fun checkaccum [] (accdefns: fdefn list) accerrs =
        (accdefns, (* rev *) accerrs) (* order? *)
        | checkaccum ((fdefn as (fdecl, fbody)) :: frest) accdefns accerrs = (
            let val accfsyms = Funtable.fromList (map #1 accdefns)
                val newerrs =
                    if isSome (Funtable.lookup accfsyms (#fname fdecl))
                    then [("*** Error: function redeclaration: "
                           ^ (#fname fdecl), (#pos fdecl))]
                    else []
                val (newfdefn, procerrs) = (checkproc newgsyms accfsyms fdefn)
            in checkaccum frest
                          (newfdefn::accdefns) (* bottom first *)
                          (newerrs @ procerrs @ accerrs) (* reverse at end *)
            end )
      val _ = debugPrint ("Global symtable: " ^ Symtable.toString newgsyms)
      val (newfdefns, funerrs) = checkaccum fdefns [] []
      val newfsyms = Funtable.fromList (map #1 newfdefns)
      (* main is treated separately (for now) *)
      val (newmain, mainerrs) = (
          case main
           of SOME (mainblock as (mainsyms, mainstmts)) =>
              let val initerrs = checkinit mainstmts
                  val (newmblock, blkerrs) = 
                      checkblock
                          (Symtable.insert (* add return type *)
                               newgsyms 
                               {name="*return*", vtype=FmUnit, sclass=Local,
                                cval=NONE})
                          newfsyms
                          mainblock 
                  val mainerrs =
                      if blkerrs @ initerrs <> []
                      then (*"*** Errors in main: " ::*) (blkerrs @ initerrs)
                      else []
              in (SOME newmblock, mainerrs)
              end
            | NONE => (NONE, []) )
  in
      (PGM {iodecls=iodecls, gdecls=gdecls, fdefns=newfdefns,
            gsyms=(SOME newgsyms), fsyms=(SOME newfsyms), main=newmain},
       gdeclerrs @ funerrs @ mainerrs)
  end
