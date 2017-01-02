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

fun printErrs errlist = ()
                     
(** Parse a program from a file, typecheck *)
fun parse file =
    let val instrm = Nonstdio.open_in_bin file
        val lexbuf = createLexerStream instrm
	val pgm    = parseReport file instrm lexbuf
	             handle exn => (BasicIO.close_in instrm; raise exn)
    in (* returns (pgm, errs) pair *)
        Fmtypes.checkprogram pgm before BasicIO.close_in instrm
    end

(* Call parser and output C version or errors *)
fun main () =
  case CommandLine.arguments ()
   of [] =>
      TextIO.output(TextIO.stdErr, "Usage: " ^ CommandLine.name()
                                   ^ " <source.fm>\n")
    | arg::_ => 
      let val (checkedpgm, errs) = parse (hd (CommandLine.arguments ()))
          val cpgm = if errs = [] (* should handle these together? *)
                     then FmtoC.printprog checkedpgm
                     else (printErrs errs; "")
      in TextIO.output(TextIO.stdErr, FmtoC.termwith "\n" errs);
         TextIO.output(TextIO.stdOut, cpgm)
      end

val _ = main ()
