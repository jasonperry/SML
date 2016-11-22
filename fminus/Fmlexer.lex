{
  open Obj Lexing Fmparse; (* Needs parser for tokens *)

 exception LexicalError of string * int * int (* (message, loc1, loc2) *)

 fun lexerError lexbuf s = 
     raise LexicalError (s, getLexemeStart lexbuf, getLexemeEnd lexbuf);

 val commentStart = ref 0;  (* Start of outermost comment being scanned *)
 
 fun commentNotClosed lexbuf =
     raise LexicalError ("Comment not terminated", 
                         !commentStart, getLexemeEnd lexbuf);
     
 val commentDepth = ref 0;  (* Current comment nesting *)

 val lineno = ref 0; 
                                
 (* Scan keywords as identifiers and use this function to distinguish them. *)
 (* If the set of keywords is large, use an auxiliary hashtable.            *)

 fun keyword s pos =
     case s of
         "var"          => VAR
       | "proc"         => PROC
       | "int"          => INTTYPE
       | "double"       => DBLTYPE
       | "bool"         => BOOLTYPE
(*       | "case"         => CASE
         | "of"           => OF *)
       | "if"           => IF
       | "then"         => THEN
       | "else"         => ELSE
       | "while"        => WHILE
       | "for"          => FOR
       | "and"          => AND
       | "or"           => OR
       | "not"          => NOT
       | "true"         => TRUE
       | "false"        => FALSE
       | "return"       => RETURN
       | "break"        => BREAK pos
       | "print"        => PRINT
       | "import"       => IMPORT
       | "main"         => MAIN
       | "indata"       => INDATA
       | "outdata"      => OUTDATA
       | _              => NAME s;

 }

rule Token = parse (* TODO: strings *)
    [` ` `\t` `\r`]     { Token lexbuf }
  | [`\n`]              { lineno := !lineno + 1; Token lexbuf }
  | `-`?[`0`-`9`]+`.`[`0`-`9`]+ { case Real.fromString (getLexeme lexbuf) of
                                   NONE   => lexerError lexbuf "internal error"
                                 | SOME d => DOUBLE d

                        }
  | `-`?[`0`-`9`]+      { case Int.fromString (getLexeme lexbuf) of
                               NONE   => lexerError lexbuf "internal error"
                             | SOME i => INT i
                        }
  | [`a`-`z``A`-`Z`][`a`-`z``A`-`Z``0`-`9`]*
                        { keyword (getLexeme lexbuf) (!lineno) }
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
  | "<<"                { LSHIFT }
  | ">>"                { RSHIFT }
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
