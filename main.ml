open Utils;;

let get_ast (i : in_channel) = 
   Parser.main Lexer.token (Lexing.from_channel i)
;; 

let i = parse_command_line () in
let result = get_ast i in
(* Ast.print_grammar 0 result;
print_newline(); *)
Code.generate_code (*!filename*) result;
print_string "\nDone";
print_newline();
exit 0
