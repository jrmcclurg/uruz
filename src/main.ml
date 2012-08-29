open Utils;;
open Code;;
open Flags;;

let get_ast (i : in_channel) = 
   Parser.main Lexer.token (Lexing.from_channel i)
;; 

print_string ("\nTEST: '"^(strip_ocaml_comments "this (* one (* two *) three *) is a test thing")^"'");

let i = parse_command_line () in
let result = get_ast i in
(* Ast.print_grammar 0 result;
print_newline(); *)
if !gen_skeleton then generate_skeleton ();
generate_code (*!filename*) result;
print_string ("\nDone");
print_newline();
exit 0
