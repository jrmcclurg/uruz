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
open Utils;;

let warning_msg =
   "(*\n"^
   " * THIS IS AN AUTO-GENERATED FILE PRODUCED BY PGG!\n"^
   " * DO NOT EDIT THIS FILE, since any changes will be\n"^
   " * lost when the build is reset via \"make clean\".\n"^
   " * This file is based on a user-specified EBNF\n"^
   " * grammar, which can be edited as desired.\n"^
   " *)"
;;

let get_filename_dir filename = 
  let dirname = Filename.dirname filename in
  let result  = (dirname^Filename.dir_sep) in
  result
;;

let get_filename filename = 
  let basename = Filename.basename filename in
  let name     = Filename.chop_extension basename in
  name
;;

let get_filename_prefix filename = 
  ((get_filename filename)^"_")
;;

let create_file filename =
  print_string ("Creating "^filename^"... ");
  flush stdout;
  open_out filename
;;

let rec flatten_grammar g = 
  print_string "flatten_grammar\n";
  match g with
  | Grammar(p,c1,c2,px,pl) ->
    let pl2 = List.fold_right (fun pr l -> (flatten_production pr)@l) (px::pl) [] in
    Grammar(p,c1,c2,List.hd pl2,List.tl pl2)
and flatten_production p = 
  print_string "flatten_production\n";
  match p with
  | Production(p,s,px,plx) -> let pl = px::plx in let (npl,nl) =
    List.fold_right (fun p (pl2,l) -> let (p2,e) = flatten_pattern s p in (p2::pl2,e@l)) pl ([],[]) in
    Production(p,s,List.hd npl,List.tl npl)::nl
and flatten_pattern prefix p = 
  print_string "flatten_pattern\n";
  match p with
  | Pattern(p,sx,slx,label,eof,c) -> let sl = sx::slx in let (nsl,nl,_) =
    List.fold_right (fun s (sl2,l,n) ->
      let (s2,e) = flatten_subpattern (prefix^"_"^(string_of_int n)) s in (s2::sl2,e@l,n-1)
    ) sl ([],[],List.length sl) in
    (Pattern(p,List.hd nsl,List.tl nsl,label,eof,c),nl)
and flatten_subpattern prefix s = 
  print_string "flatten_subpattern\n";
  if (is_subpattern_flat s) then (s,[])
  else
  match s with
  | SimpleSubpattern(p,a,o)    -> let (a2,nl) = flatten_atom prefix a in (SimpleSubpattern(p,a2,o),nl)
  | RangeSubpattern(p,a1,a2,o) ->
    let (a12,nl1) = flatten_atom (prefix^"_1") a1 in
    let (a22,nl2) = flatten_atom (prefix^"_2") a2 in
    (RangeSubpattern(p,a12,a22,o),nl1@nl2)
  | CodeSubpattern(_,_) -> (s,[])
and flatten_atom prefix a = 
  match a with
  | ChoiceAtom(p,spx,splx) ->
    let spl = spx::splx in
    let (nspl,nl,_) =
    (* here's where we expand things *)
    List.fold_right (fun sp (spl2,l,n) ->
      let (sp2,e) = flatten_subpatterns (prefix^"_"^(string_of_int n)) sp in (sp2::spl2,e@l,n-1)
    ) spl ([],[],List.length spl) in
    print_string ("flatten_atom \n"^(string_of_int (List.length nl)));
    if (List.length spl) = 1 then (a,[]) else
    let temp = List.map (fun (Subpatterns(pa,x,l)) -> Pattern(pa,x,l,None,false,None)) nspl (* TODO *) in
    (IdentAtom(p,prefix),Production(p,prefix,List.hd temp,List.tl temp)::nl)
  | _                -> (a,[])
and flatten_subpatterns prefix sp = 
  print_string "flatten_subpatterns\n";
  match sp with
  | Subpatterns(p,sx,sl) -> let (nsl,nl) =
    List.fold_right (fun s (sl2,l) -> let (s2,e) = flatten_subpattern prefix s in (s2::sl2,e@l)) (sx::sl) ([],[]) in
    (Subpatterns(p,List.hd nsl,List.tl nsl),nl)
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

let output_production_type file s =
   let temp = (
   if (is_capitalized s) then ((String.lowercase s)^"_t")
   else s ) in
   output_string file temp
;;

(* generate ast.ml *)
let rec generate_ast_code file prefix g =
  output_string file warning_msg;
  output_string file "\n\n";
  output_string file ("open "^prefix^"utils;;\n");
  output_string file "\n(* AST Data Structure *)\n\n";
  match g with Grammar(_,_,_,px,plx) ->
  let pl = px::plx in
  let _ = List.fold_left (fun flag p -> 
    generate_ast_production_code file flag p;
    true
  ) false pl in output_string file ";;\n";
and generate_ast_production_code file flag2 p =
  match p with Production(_,s,px,plx) ->
    let pl = px::plx in
    let (r,_) = List.fold_left (fun (flag,n) p ->
      generate_ast_pattern_code file s (if (List.length pl)>1 then n else 0) flag p s flag2;
      (* (true,n+1) *)
    ) (false,1) pl in ();
    if r then output_string file "\n"
and generate_ast_pattern_code file name n flag p s flag2 =
  if flag then  output_string file "\n";
  match p with Pattern(_,sx,slx,labelo,eof,c) ->
    let (ignore,label) = (match labelo with
    | None -> (false,None)
    | Some(Type(_,l)) -> (false,Some(l))
    | _ -> (true,None)) in
    if (not ignore) then (
       if (not flag) then (
          if flag2 then output_string file "\n";
          output_string file (if flag2 then " and" else "type");
          output_string file " ";
          output_production_type file s;
          output_string file " =\n";
       );
       let sl = sx::slx in
       output_string file (if (*flag*) true then "   |" else "    ");
       output_string file " ";
       (match label with
       | None -> (
         output_string file name;
         if n > 0 then (
           output_string file "_";
           output_string file (string_of_int n)
         ) else ();
       )
       | Some(label) ->
         output_string file label
       );
       output_string file " of ";
       output_production_type file "Pos";
       (*output_string file " * ";*)
       let _ = List.fold_left (fun flag s -> 
         generate_ast_subpattern_code file flag s
       ) true sl in ();
       (true,n+1)
    ) else (
       (flag,n)
    )
and generate_ast_subpattern_code file flag s =
  let f = (if flag then " * " else "") in
  match s with
  | SimpleSubpattern(_,a,Options(_,o,_,_,_,None)) ->
    output_string file f;
    if (is_subpattern_flat s) then output_string file "string" else generate_ast_atom_code file a o; true
  | SimpleSubpattern(_,a,Options(_,o,_,_,_,Some(Type(_,t)))) ->
    output_string file f;
    output_production_type file t; true
  | RangeSubpattern(_,a1,a2,Options(_,o,_,_,_,None)) ->
    output_string file f;
    output_string file "string"; true
  | RangeSubpattern(_,a1,a2,Options(_,o,_,_,_,Some(Type(_,t)))) ->
    output_string file f;
    output_production_type file t; true
  | _ -> 
     (*if (is_subpattern_flat s) then (
       output_string file f;
       output_string file "string"; true
     )
     else*) flag
  (*| CodeSubpattern(_,_) -> output_string file "???"*) (* TODO - this shouldn't happen *)
and generate_ast_atom_code file a o =
  (match o with
  | Some(PlusOp(_)) -> output_string file "("
  | _ -> () );
  let f = fun () -> (match a with
  | IdentAtom(_,s) ->
    output_production_type file s
  | StringAtom(_,_) ->
    output_string file "string"
  | CharsetsAtom(_,_) ->
    output_string file "string"
  | ChoiceAtom(_,Subpatterns(_,sub,subs),al) ->
    output_string file "(";
    let _ = List.fold_left (fun flag s -> 
      generate_ast_subpattern_code file flag s
    ) false (sub::subs) in ();
    output_string file ")"
  ) in f ();
  (match o with
  | Some(StarOp(_)) -> output_string file " list"
  | Some(PlusOp(_)) -> output_string file " * "; f (); output_string file " list)"
  | Some(QuestionOp(_)) -> output_string file " option"
  | _ -> () )
;;

(* generate utils.ml *)
let generate_utils_code file =
  output_string file "open Lexing;;\n";
  output_string file "open Parsing;;\n";
  output_string file "(* open Flags;; *)\n";
  output_string file "\n";
  output_string file "(* data type for file positions *)\n";
  output_string file "type "; output_production_type file "Pos";
     output_string file " = NoPos | Pos of string*int*int;; (* file,line,col *)\n";
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
let generate_code (*filename*) g2 =
  (*let name   = get_filename filename in*)
  let prefix = "pgg_" in
  let prefix_up = String.capitalize prefix in
  let dir    = "."^(Filename.dir_sep) in (* TODO - add support for different destination dir *)
  print_string ("THE DIR IS: '"^dir^"'\n");
  let g = flatten_grammar g2 in
  (try Unix.mkdir dir 0o755 with _ -> ());
  match g with
  | Grammar(_, c1, c2, px, plx) ->
    let file_make   = create_file (dir^prefix^"Makefile"  ) in
    (* write the Makefile contents *)
    generate_makefile_code file_make prefix;
    close_out file_make;
    print_string "done.\n";
    let file_ast    = create_file (dir^prefix^"ast.ml"    ) in
    (* write the ast.ml contents *)
    generate_ast_code file_ast prefix_up g;
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
