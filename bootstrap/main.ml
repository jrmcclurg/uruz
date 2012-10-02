open Bootstrap_main;;
open Flags;;

let i = parse_command_line () in
let result = get_ast i in
Bootstrap_ast.print_grammar_t result;
print_newline();
exit 0;;
