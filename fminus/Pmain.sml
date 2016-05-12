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

fun createLexerStream (is : BasicIO.instream) =
  Lexing.createLexer (fn buff => fn n => Nonstdio.buff_input is buff 0 n)

(* Parse a program from a file *)

fun parse file =
    let val is     = Nonstdio.open_in_bin file
        val lexbuf = createLexerStream is
	val pgm    = parseReport file is lexbuf
	             handle exn => (BasicIO.close_in is; raise exn)
        val errs   = Fmtypes.checkprogram pgm
    in 
        BasicIO.close_in is;
	(pgm, errs)
    end
