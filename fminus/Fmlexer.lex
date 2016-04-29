{
  open Obj Lexing; (* Parser; (* redundant? Gets put in the .lex.sml *) *)

datatype token = (* Was in "Parser" *)
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
  | XOR ;
  
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
(*       | "case"         => CASE
       | "of"           => OF *)
       | "if"           => IF
       | "then"         => THEN
       | "else"         => ELSE
       | "while"        => WHILE
       | "return"       => RETURN 
       | _              => NAME s;

 }

rule Token = parse (* TODO: strings *)
    [` ` `\t` `\n` `\r`]     { Token lexbuf }
  | `-`?[`0`-`9`]+      { case Int.fromString (getLexeme lexbuf) of
                               NONE   => lexerError lexbuf "internal error"
                             | SOME i => INT i
                        }  
  | [`a`-`z``A`-`Z`][`a`-`z``A`-`Z``0`-`9`]*
                        { keyword (getLexeme lexbuf) }
  | "(*"                { commentStart := getLexemeStart lexbuf;
                          commentDepth := 1; 
                          SkipComment lexbuf; Token lexbuf }
  | "->"                { DASHARROW }
  | ":="                { ASSIGN }
  | `=`                 { EQ }
  | "!="                { NE }
  | `>`                 { GT }
  | `<`                 { LT }
  | ">="                { GE }
  | "<="                { LE }
  | `+`                 { PLUS }                     
  | `-`                 { MINUS }                     
  | `*`                 { TIMES }                     
  | `/`                 { DIV }           
  | `%`                 { MOD }                    
  | `|`                 { BITOR }                     
  | `&`                 { BITAND }
  | `^`                 { XOR }
  | `(`                 { LPAR }
  | `)`                 { RPAR }
  | `[`                 { LSQUARE }
  | `]`                 { RSQUARE }
  | `{`                 { LBRACE }
  | `}`                 { RBRACE }
  | `;`                 { SEMI }
  | `:`                 { COLON }
  | `,`                 { COMMA }
  | eof                 { EOF }
  | _                   { lexerError lexbuf "Illegal symbol in input" }

and SkipComment = parse
    "*)"                { commentDepth := !commentDepth - 1;  
                          if !commentDepth = 0 then ()
                          else SkipComment lexbuf 
                        } 
   | "(*"               { commentDepth := !commentDepth + 1; 
                          SkipComment lexbuf }
   | (eof | `\^Z`)      { commentNotClosed lexbuf }
   | _                  { SkipComment lexbuf }
;