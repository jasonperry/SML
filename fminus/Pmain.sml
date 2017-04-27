(* Pmain.sml : taken from mosmllex and mosmlyac example *)

(* Parse *)

fun parseExprPlain file stream lexbuf =
    let val expr = Fmparse.Main Fmlexer.Token lexbuf
    in
	Parsing.clearParser();
	expr
    end
    handle exn => (Parsing.clearParser(); raise exn);

(* Parse; show offending program piece on error *)
fun parseReport file stream lexbuf =
    let val expr = 
	    Fmparse.Main Fmlexer.Token lexbuf
	    handle
	       Parsing.ParseError f =>
		   let val pos1 = Lexing.getLexemeStart lexbuf
		       val pos2 = Lexing.getLexemeEnd lexbuf
		   in
		       Location.errMsg (file, stream, lexbuf) 
		                       (Location.Loc(pos1, pos2))
		                       "Syntax error."
		   end
	     | Fmlexer.LexicalError(msg, pos1, pos2) =>
		   if pos1 >= 0 andalso pos2 >= 0 then
		       Location.errMsg (file, stream, lexbuf)
		                       (Location.Loc(pos1, pos2))
		                       ("Lexical error: " ^ msg)
		   else 
		       (Location.errPrompt ("Lexical error: " ^ msg ^ "\n\n");
			raise Fail "Lexical error");
    in
	Parsing.clearParser();
	expr
    end
    handle exn => (Parsing.clearParser(); raise exn);

(* Create lexer from instream *)

fun createLexerStream (instrm : BasicIO.instream) =
  Lexing.createLexer (fn buff => fn n => Nonstdio.buff_input instrm buff 0 n)

fun printErrs (errlist: errormsg list) lexinfo =
  case errlist
   of [] => ()
    | (errstr, pos)::rest => (
        Location.errMsg lexinfo pos errstr (* to stdout?! WTH... *)
        handle Fail _ => printErrs rest lexinfo ) (* compensating... *)
      
(* Call parser and output C version or errors *)
fun main () =
  case CommandLine.arguments ()
   of [] =>
      (TextIO.output(TextIO.stdErr, "Usage: " ^ CommandLine.name()
                                    ^ " <source.fm>\n");
       false)
    | fname::_ => 
      let val instrm = Nonstdio.open_in_bin fname
          val lexbuf = createLexerStream instrm
	  val pgm    = parseReport fname instrm lexbuf
	               handle exn => (BasicIO.close_in instrm; raise exn)
          val (checkedpgm, errs) = Fmtypes.checkprogram pgm
      in
          if errs = [] then
              (TextIO.output (TextIO.stdOut, FmtoC.printprog checkedpgm);
               true)
          else (printErrs errs (fname, instrm, lexbuf); 
                BasicIO.close_in instrm;
                false)
      end

val _ = if main () then Process.exit Process.success
        else Process.exit Process.failure
