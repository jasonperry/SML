%name FminusLexer;

// (* token.int: Int *)

let digit = [0-9];
let int = {digit}+;
let alpha = [a-zA-Z_];
let id = {alpha}({alpha}|{digit})*;

/* %defs (
       structure T = FminusTokens (* where from? *)
       type lex_result = T.token
       fun eof() = T.EOF
      );
*/

{id}   => (T.ID yytext);
{int}  => (T.NUM (valOf (Int.fromString yytext))); (* todo: full 32-bit *)
"+"    => (T.PLUS);
"-"    => (T.MINUS);
"*"    => (T.TIMES);
"/"    => (T.DIV);
"("    => (T.LP);
")"    => (T.RP);
" " | \n | \tb | \r
       => (continue());
.      => (print "unrecognized token: " ^ Int.fromString yytext);
