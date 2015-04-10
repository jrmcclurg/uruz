open Uruz2_utils
open Uruz2_main
open Uruz2_ast
open Flags
open Code

type foo = Bar of int | Foo of int

let () = (
let fs = parse_command_line () in
let ret = List.fold_left (fun acc (dir,f) ->
  try
    (* parse the input file *)
    (*Printf.printf ">>> dirname: %s\n" (get_abs_filename f);*)
    filename := f;
    let bin_name = get_prefix () in
    let prefix = bin_name^"_" in
    (*Printf.printf "prefix = %s (%s) (%s)\n" prefix (str_option Filename.dirname dir) f;*)
    let i = open_in f in
    let result = get_ast i in
    (*raise (General_error("x"));*)
    Flags.init_tables ();
    (* set defaults based on the poperties in input file *)
    let (result,count) = handle_props_tokens result in
    let (result,code_table) = collect_named_code result count in
    let result = inline_grammar result code_table in
    (* flatten the grammar *)
    let result = flatten_grammar result code_table in
    let result = elim_grammar result in (* eliminate quantifiers *)
    Uruz2_ast.print_grammar_t result;
    if !Flags.only_flatten then (
      exit 0
    );
    let (result,lexer_prods,lexers) = strip_lexer_grammar result count in
    let result = combine_grammar result lexers in (* combine identical lexers *)

    let (comps,gr) = get_sorted_defs result count in
    (*Printf.printf "\n\n***********************************\n\n%!";
    Printf.printf "\n\ncomps = %s\n%!" (str_x_list (fun (x,_) -> get_symbol x) comps ", ");
    print_newline();
    Printf.printf "\n\n***********************************\n\n%!";*)
    let result = typecheck result comps count gr in
    let result = restore_lexer_grammar result lexer_prods in
    Printf.printf "###################################\n";
    Uruz2_ast.print_grammar_t result;
    Printf.printf "###################################\n";
    output_code dir prefix result bin_name (get_abs_filename f) gr;
    Printf.printf "SUCCESS (%s)!\n" f;
    let o = open_out (f^".lines") in
    Hashtbl.iter (fun (file,line) set ->
      let str_pos ((i1,i2),ps) = (match ps with
      | NoPos -> ""
      | Pos(file,line,col) -> Printf.sprintf "(%d,%d)=%s,%d,%d" i1 i2 file line col) in
      Printf.fprintf o "%s,%d\t%s\n" (get_symbol file) line (str_x_list str_pos (PosSet.elements set) "\t")
    ) Flags.lines_table;
    close_out o;
    acc
  with ex ->
    Printf.printf "%s\n" (Printexc.to_string ex);
    acc+1
) 0 fs in
exit ret)
