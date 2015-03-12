open Bootstrap_utils
open Bootstrap_main
open Bootstrap_ast
open Flags
open Code

let () = (
let i = parse_command_line () in
(* parse the input file *)
let result = get_ast i in
Flags.init_tables ();
(* set defaults based on the poperties in input file *)
let (result,count) = handle_props result in
let (result,code_table) = collect_named_code result count in
let result = inline_grammar result code_table in
(* flatten the grammar *)
let result = flatten_grammar result code_table in
let result = elim_grammar result in
let (result,lexer_prods) = strip_lexer_grammar result count in
Bootstrap_ast.print_grammar_t result;
if !Flags.only_flatten then (
  exit 0
);
let comps = get_sorted_defs result count in
Printf.printf "\n\n***********************************\n\n%!";
Printf.printf "\n\ncomps = %s\n%!" (str_x_list (fun (x,_) -> get_symbol x) comps ", ");
print_newline();
Printf.printf "\n\n***********************************\n\n%!";
let result = typecheck result comps count in
Printf.printf "###################################\n";
Bootstrap_ast.print_grammar_t result;
exit 0)
