open Bootstrap_utils
open Bootstrap_main
open Flags
open Code

let () = (
let i = parse_command_line () in
(* parse the input file *)
let result = get_ast i in
(* set defaults based on the poperties in input file *)
let (result,count) = handle_props result in
let (result,code_table) = collect_named_code result count in
(* flatten the grammar *)
let result = flatten_grammar result code_table in
let graph = build_def_graph_grammar result count in
let comps = topo_sort graph in
Printf.printf "comps = %s\n%!" (str_x_list (fun x -> str_x_list get_symbol x ", ") comps "; ");
Bootstrap_ast.print_grammar_t result;
print_newline();
exit 0)
