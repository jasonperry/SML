local open Obj Lexing in


  open Obj Lexing Fmparse; (* Needs parser for tokens *)

(*datatype token = (* Was in "Parser" *)
    ASSIGN
  | BITAND
  | BITOR
  | COLON               
  | COMMA
  | DASHARROW
  | DIV
  | ELSE
  | EOF
  | EQ
  | GE
  | GT
  | IF
  | INT of int
  | INTTYPE
  | LAMBDA
  | LBRACE
  | LE
  | LPAR
  | LSQUARE
  | LT
  | MINUS
  | MOD
  | NAME of string
  | NE
  | PLUS
  | PROC
  | RBRACE
  | RETURN
  | RPAR
  | RSQUARE
  | SEMI
  | THEN
  | TIMES
  | VAR
  | WHILE
  | XOR ; *)
  
 exception LexicalError of string * int * int (* (message, loc1, loc2) *)

 fun lexerError lexbuf s = 
     raise LexicalError (s, getLexemeStart lexbuf, getLexemeEnd lexbuf);

 val commentStart = ref 0;  (* Start of outermost comment being scanned *)
 
 fun commentNotClosed lexbuf =
     raise LexicalError ("Comment not terminated", 
                         !commentStart, getLexemeEnd lexbuf);
     
 val commentDepth = ref 0;  (* Current comment nesting *)

 (* Scan keywords as identifiers and use this function to distinguish them. *)
 (* If the set of keywords is large, use an auxiliary hashtable.            *)

 fun keyword s =
     case s of
         "var"          => VAR
       | "proc"         => PROC
       | "int"          => INTTYPE
       | "bool"         => BOOLTYPE
(*       | "case"         => CASE
       | "of"           => OF *)
       | "if"           => IF
       | "import"       => IMPORT
       | "main"         => MAIN
       | "then"         => THEN
       | "else"         => ELSE
       | "while"        => WHILE
       | "and"          => AND
       | "or"           => OR
       | "not"          => NOT
       | "true"         => TRUE
       | "false"        => FALSE
       | "return"       => RETURN 
       | "print"        => PRINT
       | _              => NAME s;

 
fun action_34 lexbuf = (
 lexerError lexbuf "Illegal symbol in input" )
and action_33 lexbuf = (
 EOF )
and action_32 lexbuf = (
 COMMA )
and action_31 lexbuf = (
 COLON )
and action_30 lexbuf = (
 SEMI )
and action_29 lexbuf = (
 RBRACE )
and action_28 lexbuf = (
 LBRACE )
and action_27 lexbuf = (
 RSQUARE )
and action_26 lexbuf = (
 LSQUARE )
and action_25 lexbuf = (
 RPAR )
and action_24 lexbuf = (
 LPAR )
and action_23 lexbuf = (
 XOR )
and action_22 lexbuf = (
 BITAND )
and action_21 lexbuf = (
 BITOR )
and action_20 lexbuf = (
 MOD )
and action_19 lexbuf = (
 DIV )
and action_18 lexbuf = (
 TIMES )
and action_17 lexbuf = (
 MINUS )
and action_16 lexbuf = (
 PLUS )
and action_15 lexbuf = (
 LE )
and action_14 lexbuf = (
 GE )
and action_13 lexbuf = (
 LT )
and action_12 lexbuf = (
 GT )
and action_11 lexbuf = (
 NE )
and action_10 lexbuf = (
 EQ )
and action_9 lexbuf = (
 ASSIGN )
and action_8 lexbuf = (
 DASHARROW )
and action_7 lexbuf = (
 commentStart := getLexemeStart lexbuf;
                          commentDepth := 1; 
                          SkipComment lexbuf; Token lexbuf )
and action_6 lexbuf = (
 keyword (getLexeme lexbuf) )
and action_5 lexbuf = (
 case Int.fromString (getLexeme lexbuf) of
                               NONE   => lexerError lexbuf "internal error"
                             | SOME i => INT i
                        )
and action_4 lexbuf = (
 Token lexbuf )
and action_3 lexbuf = (
 SkipComment lexbuf )
and action_2 lexbuf = (
 commentNotClosed lexbuf )
and action_1 lexbuf = (
 commentDepth := !commentDepth + 1; 
                          SkipComment lexbuf )
and action_0 lexbuf = (
 commentDepth := !commentDepth - 1;  
                          if !commentDepth = 0 then ()
                          else SkipComment lexbuf 
                        )
and state_0 lexbuf = (
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"*" => state_40 lexbuf
 |  #"(" => state_39 lexbuf
 |  #"\^Z" => action_2 lexbuf
 |  #"\^@" => action_2 lexbuf
 |  _ => action_3 lexbuf
 end)
and state_1 lexbuf = (
 let val currChar = getNextChar lexbuf in
 if currChar >= #"A" andalso currChar <= #"Z" then  state_21 lexbuf
 else if currChar >= #"a" andalso currChar <= #"z" then  state_21 lexbuf
 else if currChar >= #"0" andalso currChar <= #"9" then  state_15 lexbuf
 else case currChar of
    #"\n" => action_4 lexbuf
 |  #"\t" => action_4 lexbuf
 |  #"\r" => action_4 lexbuf
 |  #" " => action_4 lexbuf
 |  #"}" => action_29 lexbuf
 |  #"|" => action_21 lexbuf
 |  #"{" => action_28 lexbuf
 |  #"^" => action_23 lexbuf
 |  #"]" => action_27 lexbuf
 |  #"[" => action_26 lexbuf
 |  #">" => state_20 lexbuf
 |  #"=" => action_10 lexbuf
 |  #"<" => state_18 lexbuf
 |  #";" => action_30 lexbuf
 |  #":" => state_16 lexbuf
 |  #"/" => action_19 lexbuf
 |  #"-" => state_13 lexbuf
 |  #"," => action_32 lexbuf
 |  #"+" => action_16 lexbuf
 |  #"*" => action_18 lexbuf
 |  #")" => action_25 lexbuf
 |  #"(" => state_8 lexbuf
 |  #"&" => action_22 lexbuf
 |  #"%" => action_20 lexbuf
 |  #"!" => state_5 lexbuf
 |  #"\^@" => action_33 lexbuf
 |  _ => action_34 lexbuf
 end)
and state_5 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_34);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"=" => action_11 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_8 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_24);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"*" => action_7 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_13 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_17);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_32 lexbuf
 else case currChar of
    #">" => action_8 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_15 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_5);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_32 lexbuf
 else backtrack lexbuf
 end)
and state_16 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_31);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"=" => action_9 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_18 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_13);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"=" => action_15 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_20 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_12);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"=" => action_14 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_21 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_6);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_28 lexbuf
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_28 lexbuf
 else if currChar >= #"a" andalso currChar <= #"z" then  state_28 lexbuf
 else backtrack lexbuf
 end)
and state_28 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_6);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_28 lexbuf
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_28 lexbuf
 else if currChar >= #"a" andalso currChar <= #"z" then  state_28 lexbuf
 else backtrack lexbuf
 end)
and state_32 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_5);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_32 lexbuf
 else backtrack lexbuf
 end)
and state_39 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_3);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"*" => action_1 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_40 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_3);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #")" => action_0 lexbuf
 |  _ => backtrack lexbuf
 end)
and Token lexbuf =
  (setLexLastAction lexbuf (magic dummyAction);
   setLexStartPos lexbuf (getLexCurrPos lexbuf);
   state_1 lexbuf)

and SkipComment lexbuf =
  (setLexLastAction lexbuf (magic dummyAction);
   setLexStartPos lexbuf (getLexCurrPos lexbuf);
   state_0 lexbuf)

(* The following checks type consistency of actions *)
val _ = fn _ => [action_34, action_33, action_32, action_31, action_30, action_29, action_28, action_27, action_26, action_25, action_24, action_23, action_22, action_21, action_20, action_19, action_18, action_17, action_16, action_15, action_14, action_13, action_12, action_11, action_10, action_9, action_8, action_7, action_6, action_5, action_4];
val _ = fn _ => [action_3, action_2, action_1, action_0];

end
