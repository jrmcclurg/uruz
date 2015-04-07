open Bootstrap_utils
open Bootstrap_main
open Bootstrap_ast
open Flags
open Code

type foo = Bar of int | Foo of int

let () = (
let x = Bar(123) in
match x with
| (_) -> ()
;
let fs = parse_command_line () in
let ret = List.fold_left (fun acc f ->
  try
    (* parse the input file *)
    filename := f;
    let i = open_in f in
    let result = get_ast i in
    let prefix = get_prefix () in
    (*Printf.printf "prefix = %s\n" prefix;*)
    (*raise (General_error("x"));*)
    Flags.init_tables ();
    (* set defaults based on the poperties in input file *)
    let (result,count) = handle_props result in
    let (result,code_table) = collect_named_code result count in
    let result = inline_grammar result code_table in
    (* flatten the grammar *)
    let result = flatten_grammar result code_table in
    let result = elim_grammar result in (* eliminate quantifiers *)
    Bootstrap_ast.print_grammar_t result;
    if !Flags.only_flatten then (
      exit 0
    );
    let (result,lexer_prods,lexers) = strip_lexer_grammar result count in
    let result = combine_grammar result lexers in (* combine identical lexers *)

    let (comps,gr) = get_sorted_defs result count in
    Printf.printf "\n\n***********************************\n\n%!";
    Printf.printf "\n\ncomps = %s\n%!" (str_x_list (fun (x,_) -> get_symbol x) comps ", ");
    print_newline();
    Printf.printf "\n\n***********************************\n\n%!";
    let result = typecheck result comps count gr in
    let result = restore_lexer_grammar result lexer_prods in
    Printf.printf "###################################\n";
    Bootstrap_ast.print_grammar_t result;
    Printf.printf "SUCCESS (%s)!\n" f;
    output_code prefix result;
    acc
  with ex ->
    Printf.printf "%s\n" (Printexc.to_string ex);
    acc+1
) 0 fs in
exit ret)
