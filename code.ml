(*
 * Parser Generator Generator v. 1.0
 * by Jedidiah R. McClurg
 * Northwestern University
 * 
 * code.ml
 *
 * Contains functionality for translating the AST into
 * OCaml code compatible with Yacc/Lex.
 *)

open Ast;;

let get_filename_dir filename = 
  let dirname = Filename.dirname filename in
  let result  = (dirname^Filename.dir_sep) in
  result
;;

let get_filename_prefix filename = 
  let basename = Filename.basename filename in
  let name     = Filename.chop_extension basename in
  let prefix   = (name^"_") in
  prefix
;;

let create_file filename =
  print_string ("Creating "^filename^"... ");
  flush stdout;
  open_out filename
;;

let rec flatten_grammar g = 
  print_string "flatten_grammar\n";
  match g with
  | Grammar(p,c1,c2,pl) ->
    Grammar(p,c1,c2,List.fold_right (fun pr l -> (flatten_production pr)@l) pl [])
and flatten_production p = 
  print_string "flatten_production\n";
  match p with
  | Production(p,s,pl) -> let (npl,nl) =
    List.fold_right (fun p (pl2,l) -> let (p2,e) = flatten_pattern s p in (p2::pl2,e@l)) pl ([],[]) in
    Production(p,s,npl)::nl
and flatten_pattern prefix p = 
  print_string "flatten_pattern\n";
  match p with
  | Pattern(p,sl,label,c) -> let (nsl,nl,_) =
    List.fold_right (fun s (sl2,l,n) ->
      let (s2,e) = flatten_subpattern (prefix^"_"^(string_of_int n)) s in (s2::sl2,e@l,n-1)
    ) sl ([],[],List.length sl) in
    (Pattern(p,nsl,label,c),nl)
and flatten_subpattern prefix s = 
  print_string "flatten_subpattern\n";
  match s with
  | SimpleSubpattern(p,a,o)    -> let (a2,nl) = flatten_atom prefix a in (SimpleSubpattern(p,a2,o),nl)
  | RangeSubpattern(p,a1,a2,o) ->
    let (a12,nl1) = flatten_atom (prefix^"_1") a1 in
    let (a22,nl2) = flatten_atom (prefix^"_2") a2 in
    (RangeSubpattern(p,a12,a22,o),nl1@nl2)
and flatten_atom prefix a = 
  match a with
  | ChoiceAtom(p,spl) -> let (nspl,nl,_) =
    (* here's where we expand things *)
    List.fold_right (fun sp (spl2,l,n) ->
      let (sp2,e) = flatten_subpatterns (prefix^"_"^(string_of_int n)) sp in (sp2::spl2,e@l,n-1)
    ) spl ([],[],List.length spl) in
    print_string ("flatten_atom \n"^(string_of_int (List.length nl)));
    if (List.length spl) = 1 then (a,[]) else
    (IdentAtom(p,prefix),Production(p,prefix,List.map (fun (Subpatterns(pa,l)) -> Pattern(pa,l,"",Code(NoPos,None))) nspl (* TODO *))::nl)
  | _                -> (a,[])
and flatten_subpatterns prefix sp = 
  print_string "flatten_subpatterns\n";
  match sp with
  | Subpatterns(p,sl) -> let (nsl,nl) =
    List.fold_right (fun s (sl2,l) -> let (s2,e) = flatten_subpattern prefix s in (s2::sl2,e@l)) sl ([],[]) in
    (Subpatterns(p,nsl),nl)
;;

(* generate Makefile *)
let generate_makefile_code file prefix =
  output_string file (prefix^"_main:\t\t"^prefix^"ast.cmo "^prefix^"utils.cmo "^prefix^"parser.cmo "^prefix^"lexer.cmo "^prefix^"main.cmo\n");
  output_string file ("\t\t\tocamlc -o "^prefix^"_main str.cma "^prefix^"ast.cmo "^prefix^"utils.cmo "^prefix^"parser.cmo "^prefix^"lexer.cmo "^prefix^"main.cmo\n");
  output_string file ("\n");
  output_string file (""^prefix^"main.cmo:\t\t"^prefix^"main.ml "^prefix^"parser.cmo "^prefix^"lexer.cmo\n");
  output_string file ("\t\t\tocamlc -c "^prefix^"main.ml\n");
  output_string file ("\n");
  output_string file (""^prefix^"parser.cmo:\t\t"^prefix^"parser.ml "^prefix^"parser.cmi "^prefix^"utils.cmo\n");
  output_string file ("\t\t\tocamlc -c "^prefix^"parser.ml\n");
  output_string file ("\n");
  output_string file (""^prefix^"lexer.cmo:\t\t"^prefix^"lexer.ml "^prefix^"parser.cmi "^prefix^"utils.cmo\n");
  output_string file ("\t\t\tocamlc -c "^prefix^"lexer.ml\n");
  output_string file ("\n");
  output_string file (""^prefix^"utils.cmo:\t\t"^prefix^"utils.ml "^prefix^"ast.cmo\n");
  output_string file ("\t\t\tocamlc -c "^prefix^"utils.ml\n");
  output_string file ("\n");
  output_string file (""^prefix^"parser.cmi:\t\t"^prefix^"parser.mli "^prefix^"ast.cmo\n");
  output_string file ("\t\t\tocamlc -c "^prefix^"parser.mli\n");
  output_string file ("\n");
  output_string file (""^prefix^"ast.cmo:\t\t"^prefix^"ast.ml\n");
  output_string file ("\t\t\tocamlc -c "^prefix^"ast.ml\n");
  output_string file ("\n");
  output_string file (""^prefix^"parser.ml:\t\t"^prefix^"parser.mly\n");
  output_string file ("\t\t\tocamlyacc "^prefix^"parser.mly\n");
  output_string file ("\n");
  output_string file (""^prefix^"parser.mli:\t\t"^prefix^"parser.mly\n");
  output_string file ("\t\t\tocamlyacc "^prefix^"parser.mly\n");
  output_string file ("\n");
  output_string file (""^prefix^"lexer.ml:\t\t"^prefix^"lexer.mll\n");
  output_string file ("\t\t\tocamllex "^prefix^"lexer.mll\n");
  output_string file ("\n");
  output_string file ("clean:\t\t\t\n");
  output_string file ("\t\t\trm -rf *.cm* *.mli "^prefix^"parser.ml "^prefix^"lexer.ml\n");
;;

(* generate ast.ml *)
let rec generate_ast_code file g =
  match g with Grammar(_,_,_,pl) ->
  let _ = List.fold_left (fun flag p -> 
    generate_ast_production_code file flag p;
    true
  ) false pl in ();
and generate_ast_production_code file flag p =
  match p with Production(_,s,pl) ->
    output_string file (if flag then " and" else "type");
    output_string file " ";
    output_string file (String.lowercase s);
    output_string file "_t =\n";
    let (_,_) = List.fold_left (fun (flag,n) p ->
      generate_ast_pattern_code file s (if (List.length pl)>1 then n else 0) flag p;
      (true,n+1)
    ) (false,1) pl in ();
    output_string file "\n"
and generate_ast_pattern_code file name n flag p =
  match p with Pattern(_,sl,label,c) ->
    output_string file (if flag then "   |" else "    ");
    output_string file " ";
    if label="" then (
      output_string file name;
      if n > 0 then (
        output_string file "_";
        output_string file (string_of_int n)
      ) else ();
    ) else (
      output_string file label
    );
    output_string file " of pos_t * ";
    let _ = List.fold_left (fun flag s -> 
      generate_ast_subpattern_code file flag s;
      true
    ) false sl in ();
    output_string file "\n"
and generate_ast_subpattern_code file flag s =
  output_string file (if flag then " * " else "");
  match s with
  | SimpleSubpattern(_,a,Options(_,o,_,_,_)) ->
    generate_ast_atom_code file a o
  | RangeSubpattern(_,a1,a2,Options(_,o,_,_,_)) ->
    output_string file "string"
and generate_ast_atom_code file a o =
  begin
  match a with
  | IdentAtom(_,s) ->
    output_string file s
  | StringAtom(_,_) ->
    output_string file "string"
  | CharsetsAtom(_,_) ->
    output_string file "string"
  | ChoiceAtom(_,Subpatterns(_,subs)::al) ->
    
    output_string file "(";
    let _ = List.fold_left (fun flag s -> 
      generate_ast_subpattern_code file flag s;
      true
    ) false subs in ();
    output_string file ")"
  | _ -> 
    output_string file "???" (* TODO *)
  end;
  begin
  match o with
  | Some(StarOp(_)) -> output_string file " list"
  | Some(PlusOp(_)) -> output_string file " list"
  | Some(QuestionOp(_)) -> output_string file " option"
  | _ -> ()
  end
;;

(* generate utils.ml *)
let generate_utils_code file =
  output_string file "open Lexing;;\n";
  output_string file "open Parsing;;\n";
  output_string file "open Ast;;\n";
  output_string file "\n";
  output_string file "exception Parse_error;;\n";
  output_string file "\n";
  output_string file "let parse_error s = \n";
  output_string file "  let p         = symbol_end_pos ()  in\n";
  output_string file "  let file_name = p.Lexing.pos_fname in\n";
  output_string file "  let line_num  = p.Lexing.pos_lnum  in\n";
  output_string file "  let col_num   = (p.Lexing.pos_cnum-p.Lexing.pos_bol+1) in\n";
  output_string file "  print_string (\"Parse error in '\"^file_name^\n";
  output_string file "    \"' on line \"^(string_of_int line_num)^\" col \"^(string_of_int\n";
  output_string file "    col_num)^\"!\n\"\n";
  output_string file "  )\n";
  output_string file ";;\n";
  output_string file "\n";
  output_string file "let get_current_pos () =\n";
  output_string file "  let p         = symbol_start_pos () in\n";
  output_string file "  let file_name = p.Lexing.pos_fname  in\n";
  output_string file "  let line_num  = p.Lexing.pos_lnum   in\n";
  output_string file "  let col_num   = (p.Lexing.pos_cnum-p.Lexing.pos_bol+1) in\n";
  output_string file "  Pos(file_name,line_num,col_num)\n";
  output_string file ";;\n";
  output_string file "\n";
  output_string file "let get_pos p =\n";
  output_string file "  let file_name = p.Lexing.pos_fname in\n";
  output_string file "  let line_num  = p.Lexing.pos_lnum  in\n";
  output_string file "  let col_num   = (p.Lexing.pos_cnum-p.Lexing.pos_bol+1) in\n";
  output_string file "  Pos(file_name,line_num,col_num)\n";
  output_string file ";;\n";
  output_string file "\n";
  output_string file "exception Lexing_error;;\n";
  output_string file "\n";
  output_string file "let do_newline lb = \n";
  output_string file "  Lexing.new_line lb\n";
  output_string file ";;\n";
  output_string file "\n";
  output_string file "let rec count_newlines s lb = match s with\n";
  output_string file "  | \"\" -> 0\n";
  output_string file "  | _  -> let c = String.sub s 0 1 in\n";
  output_string file "          let cs = String.sub s 1 ((String.length s)-1) in\n";
  output_string file "          if (c=\"\n\") then (do_newline lb; 1+(count_newlines cs lb))\n";
  output_string file "                      else (count_newlines cs lb)\n";
  output_string file ";;\n"
;;

(*
 * generate_code filename g
 *
 * Generates the OCaml source code for parsing the grammar
 * represented by the specified AST.
 *
 * filename          the filename of the grammar file
 * g2                the AST representing the grammar
 *)
let generate_code filename g2 =
  let dir    = get_filename_dir filename    in
  let prefix = get_filename_prefix filename in
  let g = flatten_grammar g2 in
  print_string "FLATTENED:\n";
  print_grammar 0 g;
  match g with
  | Grammar(_, c1, c2, pl) ->
    let file_make   = create_file (dir^prefix^"Makefile"  ) in
    (* write the Makefile contents *)
    generate_makefile_code file_make prefix;
    close_out file_make;
    print_string "done.\n";
    let file_ast    = create_file (dir^prefix^"ast.ml"    ) in
    (* write the ast.ml contents *)
    generate_ast_code file_ast g;
    close_out file_ast;
    print_string "done.\n";
    let file_utils  = create_file (dir^prefix^"utils.ml"  ) in
    (* write the utils.ml contents *)
    generate_utils_code file_utils;
    close_out file_utils;
    print_string "done.\n";
    let file_parser = create_file (dir^prefix^"parser.mly") in
    (* write the parser.mly contents *)
    close_out file_parser;
    print_string "done.\n";
    let file_lexer  = create_file (dir^prefix^"lexer.mll" ) in
    (* write the lexer.mll contents *)
    close_out file_lexer;
    print_string "done.\n";
    let file_main   = create_file (dir^prefix^"main.ml"   ) in
    (* write the main.ml contents *)
    close_out file_main;
    print_string "done.\n"
;;
