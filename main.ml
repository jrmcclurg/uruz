let toss x = ();
(* File calc.ml *)
print_string "this is a test\n";;
flush stdout;;
let _ =
let lexbuf = Lexing.from_channel stdin in
let result = Parser.main Lexer.token lexbuf in
print_string "Result=\n"; Ast.print_grammar 0 result; print_newline(); flush stdout;
print_string "Done";
exit 0
