{
   open Parser;; (* The type token is defined in parser.mli *)
   open Ast;;
   open Utils;;
}
rule token = parse
  [' ' '\t'] {token lexbuf } (* skip blanks *)
| ['\r'] { token lexbuf } (* skip blanks *)
| ['\n'] { do_newline lexbuf; token lexbuf }
| ['0'-'9']+ as s { INT(int_of_string s) }
| "eof" { ENDFILE }
| "left" { LEFT }
| "right" { RIGHT }
| "unary" { UNARY }
| '/' '/' [^'\n']* { token lexbuf }
| ['A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9']* as s { IDENT(s) }
| ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']* as s { TYPENAME(s) }
| '{' { let p = Lexing.lexeme_start_p lexbuf in
        let s = code 0 "" lexbuf in
        CODE(p, s) }
| "/*" { comment 0 lexbuf }
| '[' (([^'\\' ']']* ('\\' _)*)* as s) ']' { CHARSET(Utils.string_of_string ("\""^s^"\"")) }
| '"' (([^'\\' '"']* ('\\' _)*)*) '"' as s { STRINGQUOT(Utils.string_of_string s) }
| '\'' (([^'\\' '\''] |
         ('\\' ('\\'|'"'|'\''|'n'|'r'|'t'|'b')) |
         ('\\' ['0'-'9'] ['0'-'9'] ['0'-'9']) )) '\'' as s { CHARQUOT(Utils.char_of_string s) }
| '-' '>' { ARROW }
| '|' { BAR }
| ';' { SEMI }
| ':' { COLON }
| ',' { COMMA }
| '*' { STAR }
| '+' { PLUS }
| '?' { QUESTION }
| '@' { AMP }
| '=' { EQUAL }
| '$' { DOLLAR }
| '_' { WILDCARD }
| '\\' { DIFF }
| '<' { LANGLE }
| '>' { RANGLE }
| '{' { LBRACK }
| '}' { RBRACK }
| '(' { LPAREN }
| ')' { RPAREN }
| ".." { RECUR }
| '.' { DOT }
| eof { EOF }
| _ { lex_error "lexing error" lexbuf }

and code n s = parse
| '{' { code (n+1) (s^"{") lexbuf }
| '}' { if (n=0) then s else code (n-1) (s^"}") lexbuf }
| _ as c { if c='\n' then do_newline lexbuf;
           code n (Printf.sprintf "%s%c" s c) lexbuf }

and comment n = parse
| "/*" { comment (n+1) lexbuf }
| "*/" { if (n=0) then token lexbuf else comment (n-1) lexbuf }
| _ as c { if c='\n' then do_newline lexbuf;
           comment n lexbuf }
