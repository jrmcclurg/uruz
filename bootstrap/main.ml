open Bootstrap_main
open Flags
open Code

let () = (
let i = parse_command_line () in
(* parse the input file *)
let result = get_ast i in
(* set defaults based on the poperties in input file *)
handle_props result;
(* flatten the grammar *)
let result = flatten_grammar result in
Bootstrap_ast.print_grammar_t result;
print_newline();
exit 0)
