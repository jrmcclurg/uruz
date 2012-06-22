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
open Flags;;

module SubpatternHashtbl = Hashtbl.Make(struct
                                           type t = subpattern
                                           let equal a b = (reloc_subpattern a) = (reloc_subpattern b)
                                           let hash s = Hashtbl.hash (reloc_subpattern s)
                                        end);;

let output_warning_msg (f : out_channel) (s1 : string) (s2 : string) (s3 : string) : unit =
   output_string f (s1^"\n"^
   s2^" THIS IS AN AUTO-GENERATED FILE PRODUCED BY PGG!\n"^
   s2^" DO NOT EDIT THIS FILE, since any changes will be\n"^
   s2^" lost when the build is reset via \"make clean\".\n"^
   s2^" This file is based on a user-specified EBNF\n"^
   s2^" grammar, which can be edited as desired.\n"^
   s3)
;;

let get_assoc_str (a : assoc option) (pr : int option) : ((string*int) option) =
   match (a,pr) with
   | (Some(LeftAssoc(p)),None) -> Some("left",!default_prec)
   | (Some(LeftAssoc(p)),Some(i)) -> Some("left",i)
   | (Some(RightAssoc(p)),None) -> Some("right",!default_prec)
   | (Some(RightAssoc(p)),Some(i)) -> Some("right",i)
   | (Some(UnaryAssoc(p)),None) -> Some("nonassoc",!default_prec)
   | (Some(UnaryAssoc(p)),Some(i)) -> Some("nonassoc",i)
   | (None,Some(i)) -> Some(!default_assoc,i)
   | _ -> None
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
  | Pattern(p,slx,label,eof,c,i,asc) -> let sl = slx in let (nsl,nl,_,_) =
    let len = List.fold_left (fun res s ->
       match s with
       | CodeSubpattern(_,_) -> res
       | _ -> res+1
    ) 0 sl in
    List.fold_right (fun s (sl2,l,n,flag) ->
       (* NOTE - pull out range patterns *)
       (* NOTE - pull out *,+,?-modified stuff *)
       let new_pref = (prefix^"_"^(string_of_int n)) in
       match s with
       | RangeSubpattern(rp,ra1,ra2,ro) ->
          if flag then (s::sl2, l, n-1, false)
          else ((SimpleSubpattern(rp,IdentAtom(rp,new_pref),Options(rp,None,None,None,false,None,None)))::sl2,
          [Production(rp,new_pref,Pattern(rp,[s],None,false,None,None,None),[])]@l, n-1, false)
       | SimpleSubpattern(rp,IdentAtom(rp2,name),Options(rp3,Some(o),o1,o2,o3,typo,o5)) ->
          let the_typename = (get_production_type name) in
          let (nm,e,tp) = (match o with
          | StarOp(_) ->
             let nm = (new_pref^"_list") in
             (nm,[Production(rp,nm,Pattern(rp,[],Some(EmptyType(rp)),false,Some(Code(rp," [] ")),None,None),
                                  [Pattern(rp,[s;
                                  SimpleSubpattern(rp,IdentAtom(rp,nm),Options(rp,None,None,None,false,None,None))],
                                  Some(EmptyType(rp)),false,Some(Code(rp," $1::$2 ")),None,None)])],
              (the_typename^" list"))
          | PlusOp(_) ->
             let nm = (new_pref^"_nlist") in
             (nm,[Production(rp,nm,Pattern(rp,[s],Some(EmptyType(rp)),false,Some(Code(rp," ($1,[]) ")),None,None),
                                  [Pattern(rp,[s;
                                  SimpleSubpattern(rp,IdentAtom(rp,nm),Options(rp,None,None,None,false,None,None))],
                                  Some(EmptyType(rp)),false,Some(Code(rp," let (h,l) = $2 in ($1,h::l) ")),None,None)])],
              ("("^the_typename^" * "^the_typename^" list)"))
          | QuestionOp(_) -> ((new_pref^"_opt"),[],"")
          ) in
          let use_type = (match typo with
          | None -> Some(Type(rp3,tp))
          | _ -> typo) in
          ((SimpleSubpattern(rp,IdentAtom(rp2,nm),Options(rp3,None,o1,o2,o3,use_type,o5)))::sl2, e@l, n-1, false)
       | CodeSubpattern(_,_) -> (s::sl2, l, n, true)
       | _ ->
          let (s2,e) = flatten_subpattern new_pref s in (s2::sl2,e@l,n-1,false)
    ) sl ([],[],len,true) in
    (Pattern(p,nsl,label,eof,c,i,asc),nl)
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
    let temp = List.map (fun (Subpatterns(pa,x,l)) -> Pattern(pa,(x::l),None,false,None,None,None)) nspl (* TODO *) in
    (IdentAtom(p,prefix),Production(p,prefix,List.hd temp,List.tl temp)::nl)
  | _                -> (a,[])
and flatten_subpatterns prefix sp = 
  print_string "flatten_subpatterns\n";
  match sp with
  | Subpatterns(p,sx,sl) -> let (nsl,nl) =
    List.fold_right (fun s (sl2,l) -> let (s2,e) = flatten_subpattern prefix s in (s2::sl2,e@l)) (sx::sl) ([],[]) in
    (Subpatterns(p,List.hd nsl,List.tl nsl),nl)
;;

let rec get_terminals_grammar (g : grammar)
                              (h : (string*((string*int) option)*string option*pos) SubpatternHashtbl.t) : unit =
   match g with
   | Grammar(_,_,_,pr,prl) ->
      List.iter (fun pr ->
         get_terminals_production pr h
      ) (pr::prl)

and get_terminals_production (pr : production)
                             (h : (string*((string*int) option)*string option*pos) SubpatternHashtbl.t) : unit =
   match pr with
   | Production(_,name,pa,pal) ->
      let b = ((List.length pal) = 0) in
      let _ = List.fold_left (fun i pa ->
         get_terminals_pattern pa (if b then name else (name^"_"^(string_of_int i))) h;
         i+1
      ) 1 (pa::pal) in ()

and get_terminals_pattern (pa : pattern) (s : string)
                          (h : (string*((string*int) option)*string option*pos) SubpatternHashtbl.t) : unit =
   match pa with
   | Pattern(ps,spl,t,_,_,i,asc) -> 
      let name = (to_token_case (match t with
      | Some(Type(_,s)) -> s
      | _ -> s)) in
      let x = get_assoc_str asc i in
      (match x with
      | None -> ()
      | _ -> SubpatternHashtbl.replace h
                (SimpleSubpattern(NoPos,IdentAtom(NoPos,name),Options(NoPos,None,None,None,false,None,None)))
                ((name^"_0"),x,None,ps)); (* TODO - does this work? *)
      let b = ((List.length spl) = 1) in
      let _ = List.fold_left (fun n sp ->
         get_terminals_subpattern sp (name^(if b then "" else ("_"^(string_of_int n)))) h n;
      ) 1 spl in ()

and get_terminals_subpattern (sp : subpattern) (s : string)
                             (h : (string*((string*int) option)*string option*pos) SubpatternHashtbl.t) (n : int) : int =
   match sp with
   | SimpleSubpattern(_,IdentAtom(_,_),Options(ps,_,prec,a,_,_,_)) ->
      let x = (get_assoc_str a prec) in
      (match x with
      | Some(_) -> die_error ps "cannot set options for non-terminal" (* TODO - this should never happen (done in parser) *)
      | _ -> ());
      n+1
   | SimpleSubpattern(_,_,Options(ps,_,prec,a,_,Some(Type(_,t)),_)) ->
      let x = (get_assoc_str a prec) in
      SubpatternHashtbl.replace h sp (s,x,Some(t),ps);
      n+1
   | SimpleSubpattern(_,_,Options(ps,_,prec,a,_,Some(EmptyType(_)),_)) ->
      let x = (get_assoc_str a prec) in
      SubpatternHashtbl.replace h sp (s,x,None,ps);
      n+1
   | SimpleSubpattern(_,_,Options(ps,_,prec,a,_,None,_)) ->
      let x = (get_assoc_str a prec) in
      SubpatternHashtbl.replace h sp (s,x,get_subpattern_default_type sp,ps);
      n+1
   | RangeSubpattern(_,_,_,Options(ps,_,prec,a,_,Some(Type(_,t)),_)) ->
      let x = (get_assoc_str a prec) in
      SubpatternHashtbl.replace h sp (s,x,Some(t),ps);
      n+1
   | RangeSubpattern(_,_,_,Options(ps,_,prec,a,_,Some(EmptyType(_)),_)) ->
      let x = (get_assoc_str a prec) in
      SubpatternHashtbl.replace h sp (s,x,None,ps);
      n+1
   | RangeSubpattern(_,_,_,Options(ps,_,prec,a,_,None,_)) ->
      let x = (get_assoc_str a prec) in
      SubpatternHashtbl.replace h sp (s,x,get_subpattern_default_type sp,ps);
      n+1
   | CodeSubpattern(_,_) -> n
;;

let generate_makefile_vars file =
   let olevel = (match !opt_level with
   | None -> ""
   | Some(l) -> " -ccopt -O"^l) in
   let static = (match !compile_static with
   | false -> ""
   | true -> " -ccopt -static") in
   let debug = (match !debug_symbols with
   | false -> ""
   | true -> " -p -g") in
   let (command,xo,xa) = (match !compiler with
   | OCamlC -> ("ocamlc","o","")
   | OCamlOpt -> ("ocamlopt"^olevel^static^debug, "x", "x")
   | OCamlCp -> ("ocamlcp -p a", "o", "")) in
   output_string file ("OCAMLC = "^command^"\n");
   output_string file ("CMO = cm"^xo^"\n");
   output_string file ("CMA = cm"^xa^"a\n");
;;

(* generate Makefile *)
let generate_makefile_code file prefix =
   output_warning_msg file "#" "#" "#";
   output_string file "\n\n";
   output_string file "ifndef OCAMLC\n";
   generate_makefile_vars file;
   output_string file "endif\n";
   output_string file (prefix^"main.$(CMO):\t"^prefix^"main.ml "^prefix^"parser.$(CMO) "^prefix^"lexer.$(CMO) "^
                      prefix^"ast.$(CMO) "^prefix^"utils.$(CMO)\n");
   output_string file ("\t\t$(OCAMLC) -c "^prefix^"main.ml\n");
   output_string file ("\n");
   output_string file (""^prefix^"parser.$(CMO):\t"^prefix^"parser.ml "^prefix^"parser.cmi "^
                      prefix^"utils.$(CMO)\n");
   output_string file ("\t\t$(OCAMLC) -c "^prefix^"parser.ml\n");
   output_string file ("\n");
   output_string file (""^prefix^"lexer.$(CMO):\t"^prefix^"lexer.ml "^prefix^"parser.cmi "^
                      prefix^"ast.$(CMO) "^prefix^"utils.$(CMO)\n");
   output_string file ("\t\t$(OCAMLC) -c "^prefix^"lexer.ml\n");
   output_string file ("\n");
   output_string file (""^prefix^"parser.cmi:\t"^prefix^"parser.mli "^prefix^"ast.$(CMO) "^
                      prefix^"utils.$(CMO)\n");
   output_string file ("\t\t$(OCAMLC) -c "^prefix^"parser.mli\n");
   output_string file ("\n");
   output_string file (""^prefix^"ast.$(CMO):\t"^prefix^"ast.ml "^prefix^"utils.$(CMO)\n");
   output_string file ("\t\t$(OCAMLC) -c "^prefix^"ast.ml\n");
   output_string file ("\n");
   output_string file (""^prefix^"parser.ml:\t"^prefix^"parser.mly\n");
   output_string file ("\t\tocamlyacc "^prefix^"parser.mly\n");
   output_string file ("\n");
   output_string file (""^prefix^"parser.mli:\t"^prefix^"parser.mly\n");
   output_string file ("\t\tocamlyacc "^prefix^"parser.mly\n");
   output_string file ("\n");
   output_string file (""^prefix^"lexer.ml:\t"^prefix^"lexer.mll\n");
   output_string file ("\t\tocamllex "^prefix^"lexer.mll\n");
   output_string file ("\n");
   output_string file (""^prefix^"utils.$(CMO):\t"^prefix^"utils.ml\n");
   output_string file ("\t\t$(OCAMLC) -c "^prefix^"utils.ml\n");
   output_string file ("\n");
  output_string file (prefix^"clean:\t\t\t\n");
  output_string file ("\t\t\trm -rf *.cm* *.mli "^prefix^"parser.ml "^prefix^"lexer.ml\n");
;;

(* generate ast.ml *)
let rec generate_ast_code file prefix g =
  output_warning_msg file "(*" " *" " *)";
  output_string file "\n\n";
  output_string file ("open "^prefix^"utils;;\n");
  output_string file "\n(* AST Data Structure *)\n\n";
  match g with Grammar(_,_,_,px,plx) ->
  let pl = px::plx in
  let _ = List.fold_left (fun flag p -> 
    generate_ast_production_code file prefix flag p;
    true
  ) false pl in output_string file ";;\n";
and generate_ast_production_code file prefix flag2 p =
  match p with Production(_,s,px,plx) ->
    let pl = px::plx in
    let (r,_) = List.fold_left (fun (flag,n) p ->
      generate_ast_pattern_code file prefix s (if (List.length pl)>1 then n else 0) flag p s flag2;
      (* (true,n+1) *)
    ) (false,1) pl in ();
    if r then output_string file "\n"
and generate_ast_pattern_code file prefix name n flag p s flag2 =
  if flag then  output_string file "\n";
  match p with Pattern(_,slx,labelo,eof,c,_,_) ->
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
       let sl = slx in
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
       if (not (is_pattern_empty p)) then (
       let _ = List.fold_left (fun flag s -> 
         generate_ast_subpattern_code file prefix flag s
       ) true sl in () );
       (true,n+1)
    ) else (
       (flag,n)
    )
and generate_ast_subpattern_code (file : out_channel) (prefix : string) (flag : bool) (s : subpattern) : bool =
  let f = (if flag then " * " else "") in
  match s with
  | SimpleSubpattern(ps,a,Options(_,o,_,_,_,None,_)) ->
    output_string file f;
    (* TODO - i dont think this will always be a string *)
    if (is_subpattern_flat s) then (
       let t = (get_subpattern_default_type s) in
       (match t with
       | None -> false (* NOTE: there is at least one subpattern that is non-empty, so printing the " * " is okay *)
       | Some(s) ->  output_string file s; true);
    ) else (generate_ast_atom_code file prefix a o; true)
  | SimpleSubpattern(_,a,Options(_,o,_,_,_,Some(Type(_,t)),_)) ->
    output_string file f;
    output_string file (str_remove_from_front t (prefix^"ast."));
    true
  | RangeSubpattern(_,a1,a2,Options(_,o,_,_,_,None,_)) ->
    output_string file f;
    (* TODO - will this will always be a string? *)
    output_string file "string"; true
  | RangeSubpattern(_,a1,a2,Options(_,o,_,_,_,Some(Type(_,t)),_)) ->
    output_string file f;
    output_string file (str_remove_from_front t (prefix^"ast."));
    true
  | _ -> 
     (*if (is_subpattern_flat s) then (
       output_string file f;
       output_string file "string"; true
     )
     else*) flag
  (*| CodeSubpattern(_,_) -> output_string file "???"*) (* TODO - this shouldn't happen *)
and generate_ast_atom_code file prefix a o =
  (match o with
  | Some(PlusOp(_)) -> output_string file "("
  | _ -> () );
  let f = fun () -> (match a with
  | IdentAtom(_,s) ->
    output_production_type file s
  | StringAtom(ps,st) ->
    (* TODO - will this always be a string? *)
    let t =  (get_atom_default_type a) in
    (match t with
    | None -> die_error ps "empty default type" (* TODO - this should never happen *)
    | Some(t) -> output_string file t)
  | CharsetsAtom(ps,_) ->
    (* TODO - will this always be a string? *)
    let t = (get_atom_default_type a) in
    (match t with
    | None -> die_error ps "empty default type"
    | Some(t) -> output_string file t)
  | ChoiceAtom(_,Subpatterns(_,sub,subs),al) ->
    output_string file "(";
    let _ = List.fold_left (fun flag s -> 
      generate_ast_subpattern_code file prefix flag s
    ) false (sub::subs) in ();
    output_string file ")"
  ) in f ();
  (match o with
  | Some(StarOp(_)) -> output_string file " list"
  | Some(PlusOp(_)) -> output_string file " * "; f (); output_string file " list)"
  | Some(QuestionOp(_)) -> output_string file " option"
  | _ -> () )
;;

(* generate parser.mly *)
let generate_parser_code file prefix g (h : ((string*((string*int) option)*string option*pos) SubpatternHashtbl.t)) =
   let toks = ((Hashtbl.create 100) : (string option,string list) Hashtbl.t) in (* type,token_names *)
   let assocs = ((Hashtbl.create 100) : (int,(string*string list)) Hashtbl.t) in (* prec,assoc,token_names *)
   match g with
   | Grammar(p,header,footer,(Production(p2,name,pa,pal) as prodf),prodl) ->
   output_warning_msg file "/*" " *" " */";
   output_string file "\n\n";
   output_string file "%{\n";
   output_string file ("   open "^prefix^"ast;;\n");
   output_string file ("   open "^prefix^"utils;;\n");
   output_string file "%}\n\n";
   SubpatternHashtbl.iter (fun k (s,assoc_str,ty,ps) -> 
      let a = (try Hashtbl.find toks ty with _ -> []) in
      Hashtbl.replace toks ty (s::a);
      (match assoc_str with
      | None -> ()
      | Some((asc2,prec2)) ->
         let (asc,sl) = (try Hashtbl.find assocs prec2 with _ -> (asc2,[])) in
         if (asc <> asc2) then die_error ps ("terminal symbol "^s^" cannot have "^
                                                asc2^" assoc at precedence "^(string_of_int prec2));
         Hashtbl.replace assocs prec2 (asc,(s::sl));
      );
   ) h;
   (*let tab2 = List.sort
   (fun (_,p1,_) (_,p2,_) ->
      let i1 = (match p1 with
      | None -> Pervasives.min_int
      | Some(i) -> i) in
      let i2 = (match p2 with
      | None -> Pervasives.min_int
      | Some(i) -> i) in
      compare i1 i2
   ) tab in*)
   (* TODO - sort the following hashtable by the type name *)
   output_string file "%token EOF\n";
   Hashtbl.iter (fun ty sl ->
      let t = (match ty with
      | None -> ""
      | Some(s) -> " <"^s^">") in
      let o = ("%token"^t) in
      let olen = String.length o in
      output_string file o;
      let _ = List.fold_left (fun n s ->
         let x = (" "^s) in 
         let n2 = n+(String.length x) in
         let n3 = if n2 > !page_width then (output_string file "\n"; output_spaces file olen ""; 0) else n2 in
         output_string file x; n3
      ) olen (List.sort (String.compare) sl) in
      output_string file "\n";
   ) toks;
   output_string file "\n";
   let assocl = Hashtbl.fold (fun i (s,sl) res ->
      (i,s,sl)::res
   ) assocs [] in
   (* TODO - add the line wrap for this loop, and sort each list *)
   List.iter (fun (i,s,sl) ->
      output_string file ("%"^s);
      List.iter (fun s ->
         output_string file (" "^s);
      ) sl;
      output_string file (" /* "^(string_of_int i)^" */\n");
   ) (List.sort (fun (i1,_,_) (i2,_,_) -> compare i2 i1) assocl);
   (*List.iter (fun (s,prec,t) ->
      output_string file ("%token "^t^s^" /* "^(match prec with Some(p) -> string_of_int p | _ -> "")^" */\n")
   ) tab2;*)
   output_string file "\n";
   output_string file "%start main /* the entry point */\n";
   output_string file ("%type <"^prefix^"ast."^(get_production_type name)^"> main\n");
   output_string file "%%\n";
   let _ = List.fold_left (fun n ((Production(p2,name,pa,pal)) as pr) ->
      (* TODO - make sure (via parser?) that the first production is non-empty *)
      if (not (is_production_empty pr)) then (
         let name2 = if n = 1 then "main" else (output_string file "\n"; (get_production_type name)) in
         output_string file (name2^":\n");
         let _ = List.fold_left (fun k (Pattern(_,sl,_,ef,cd,i,asc)) ->
            match cd with
            | None -> k
            | _ -> (
               output_string file "   |";
               let _ = List.fold_left (fun j s ->
                  let str = (try let (x,_,_,_) = SubpatternHashtbl.find h s in (" "^x) with _ -> 
                     match s with
                     | SimpleSubpattern(_,IdentAtom(_,name),_) -> (" "^(get_production_type name))
                     | CodeSubpattern(_,_) -> ""
                     | _ -> "XXX" (* TODO - this should never happen - do error? *)
                  ) in
                  output_string file (str);
                  j+1
               ) 1 sl in
               if ef then output_string file " EOF";
               (* TODO - add precedence *)
               output_string file " {";
               (match cd with
               | None -> output_string file " "
               | Some(Code(_,s)) -> output_string file s);
               output_string file "}\n";
               k+1
            )
         ) 1 (pa::pal) in 
         output_string file ";\n";
         n+1
      ) else n
   ) 1 (prodf::prodl) in ();
   output_string file "\n";
   output_string file "%%\n";
   output_string file "(* footer code *)\n";
;;

(* generate lexer.mll *)
let rec generate_lexer_code file prefix g (h : (string*((string*int) option)*string option*pos) SubpatternHashtbl.t) =
   output_warning_msg file "(*" " *" " *)";
   output_string file "\n\n";
   output_string file "{\n";
   output_string file ("   open "^prefix^"parser;; (* The type token is defined in parser.mli *)\n");
   output_string file ("   open "^prefix^"ast;;\n");
   output_string file ("   open "^prefix^"utils;;\n");
   output_string file "}\n";
   output_string file "rule token = parse\n";
   (* TODO XXX - sort and all that - I THINK THE ORDER NEEDS TO CORRESPOND TO FILE ORDER *)
   SubpatternHashtbl.iter (fun s (name,_,ty,p) ->
      let (cd) = (match s with
      | SimpleSubpattern(_,StringAtom(_,s1),Options(_,_,_,_,_,_,cd)) -> (cd)
      | SimpleSubpattern(_,ChoiceAtom(_,sp,spl),Options(_,_,_,_,_,_,cd)) -> (cd)
      | _ -> (None) (* TODO - fill this in *)
      ) in
      let (bef,aft) = (match (ty,cd) with
      | (None,None) -> ("",name)
      | (None,Some(Code(_,s) as c)) -> ("",if (is_code_empty c) then "token lexbuf" else name)
      | (Some(s),None) -> ("",(name^"(s)"))
      | (Some(_),Some(Code(_,s) as c)) ->
         ("",if (is_code_empty c) then "token lexbuf" else ("let t = "^s^" in ignore t; "^name^"(t)"))) in
      match s with
      | SimpleSubpattern(_,IdentAtom(_,_),_) -> ()
      | _ ->
         output_string file "| ";
         let _ = generate_lexer_subpattern_code file s in
         output_string file (" as s { ignore s; "^aft^" }\n");
   ) h;
   output_string file "| eof { EOF }\n";
   output_string file "| _ { lex_error \"lexing error\" lexbuf }";

and generate_lexer_atom_code file a : bool =
   match a with
   | IdentAtom(ps,s) -> false (* NOTE - this is only used to provide the %prec things to parser.mly,
                               *        so just ignore it*)
   | StringAtom(_,s) -> output_string file ("\""^s^"\""); true
   | CharsetsAtom(_,SingletonCharsets(_,c)) -> generate_lexer_charset_code file c; true
   | CharsetsAtom(_,DiffCharsets(_,c1,c2)) ->
      generate_lexer_charset_code file c1;
      output_string file " # ";
      generate_lexer_charset_code file c2;
      true
   | ChoiceAtom(_,s,sl) ->  (* NOTE - each os the subpattern lists is non-empty *)
      output_string file "(";
      let _ = List.fold_left (fun flag s ->
         if flag then output_string file " | ";
         let _ = generate_lexer_subpatterns_code file s in ();
         true
      ) false (s::sl) in ();
      output_string file ")";
      true

and generate_lexer_subpatterns_code file sp =
   match sp with
   | Subpatterns(_,s,sl) ->
      let (_,res) = List.fold_left (fun (flag,res) s ->
         if flag then output_string file " ";
         let flag2 = generate_lexer_subpattern_code file s in
         (flag2,(res||flag2))
      ) (true,false) (s::sl) in
      res

and generate_lexer_subpattern_code file s : bool =
   (* TODO - what about code subpatterns, i.e. empty patterns *)
   match s with
   | SimpleSubpattern(_,a,Options(_,o,_,_,_,_,_)) -> 
      let r = generate_lexer_atom_code file a in
      (match o with
      | Some(StarOp(_)) -> output_string file "*"
      | Some(PlusOp(_)) -> output_string file "+"
      | Some(QuestionOp(_)) -> output_string file "?"
      | _ -> ());
      r
   | RangeSubpattern(_,a1,a2,_) -> generate_lexer_atom_code file a1  (* TODO - the rest goes in the semantic rule *)
   | CodeSubpattern(_,_) -> false

and generate_lexer_charset_code file c =
   match c with
   | WildcardCharset(_) -> output_string file "_"
   | SingletonCharset(_,c) -> output_string file ("'"^(Char.escaped c)^"'")  (* TODO - escaped!!!! *)
   | ListCharset(_,cl,inv) ->
      output_string file "[";
      let t = (if inv then (output_string file "^"; true) else false) in
      let _ = List.fold_left (fun flag c ->
         if flag then output_string file " ";
         generate_lexer_chars_code file c;
         true
      ) t cl in
      output_string file "]";

and generate_lexer_chars_code file c =
   match c with
   | SingletonChars(_,c) -> output_string file ("'"^(Char.escaped c)^"'") (* TODO - escaped!! *)
   | RangeChars(_,c1,c2) -> 
      output_string file ("'"^(Char.escaped c1)^"'-'"^(Char.escaped c2)^"'")
;;
(* TODO - handle ?,+,* options for the terminals *)

(* TODO - handle the eof.  Also, what is the bool in Options? *)

let generate_main_code file prefix g =
   output_warning_msg file "(*" " *" " *)";
   output_string file "\n\n";
   output_string file ("open "^prefix^"parser;;\n");
   output_string file ("open "^prefix^"lexer;;\n");
   output_string file "\n";
   output_string file "let get_ast (i : in_channel) = \n";
   output_string file ("   "^prefix^"parser.main "^prefix^"lexer.token (Lexing.from_channel i)\n");
   output_string file ";;\n";
;;

(* generate utils.ml *)
let generate_utils_code file g =
   match g with
   | Grammar(p,header,footer,_,_) ->
  output_string file "open Lexing;;\n";
  output_string file "open Parsing;;\n";
  output_string file "(* open Flags;; *)\n";
  output_string file "\n";
  (match header with
  | None -> ()
  | Some(Code(_,s)) -> output_string file (s^"\n"));
  let p = (get_production_type "Pos") in
  output_string file "(* data type for file positions *)\n";
  output_string file ("type "^p^" = NoPos | Pos of string*int*int;; (* file,line,col *)\n");
  output_string file "\n";
  output_string file "exception Parse_error;;\n";
  output_string file "exception Lexing_error;;\n";
  output_string file "\n";
  output_string file "(* do_error p s\n";
  output_string file " *\n";
  output_string file " * Print error message\n";
  output_string file " *\n";
  output_string file " * p - the location of the error\n";
  output_string file " * s - the error message\n";
  output_string file " *\n";
  output_string file " * returns unit\n";
  output_string file " *)\n";
  output_string file ("let do_error (p : "^p^") (s : string) : unit =\n");
  output_string file "   print_string \"Error\";\n";
  output_string file "   print_string (match p with\n";
  output_string file "   | NoPos -> \"\"\n";
  output_string file "   | Pos(file_name,line_num,col_num) -> (\" in '\"^file_name^\n";
  output_string file "    \"' on line \"^(string_of_int line_num)^\" col \"^(string_of_int\n";
  output_string file "    col_num))\n";
  output_string file "   );\n";
  output_string file "   print_string (\": \"^s^\"\\n\")\n";
  output_string file ";;\n";
  output_string file "\n";
  output_string file ("let die_error (p : "^p^") (s : string) =\n");
  output_string file "   do_error p s;\n";
  output_string file "   exit 1;\n";
  output_string file ";;\n";
  output_string file "\n";
  output_string file "(* dies with a general position-based error *)\n";
  output_string file "let pos_error (s : string) (p : position) = \n";
  output_string file "   let file_name = p.Lexing.pos_fname in\n";
  output_string file "   let line_num  = p.Lexing.pos_lnum  in\n";
  output_string file "   let col_num   = (p.Lexing.pos_cnum-p.Lexing.pos_bol+1) in\n";
  output_string file "   let ps        = Pos(file_name,line_num,col_num) in\n";
  output_string file "   do_error ps s\n";
  output_string file ";;\n";
  output_string file "\n";
  output_string file "(* dies with a parse error s *)\n";
  output_string file "let parse_error (s : string) = \n";
  output_string file "   pos_error s (symbol_end_pos ());\n";
  output_string file "   raise Parse_error\n";
  output_string file ";;\n";
  output_string file "\n";
  output_string file "(* dies with a lexing error *)\n";
  output_string file "let lex_error (s : string) (lexbuf : Lexing.lexbuf) = \n";
  output_string file "   pos_error s (Lexing.lexeme_end_p lexbuf);\n";
  output_string file "   raise Lexing_error\n";
  output_string file ";;\n";
  output_string file "\n";
  output_string file "(* gets a pos data structure using the current lexing pos *)\n";
  output_string file "let get_current_pos () =\n";
  output_string file "   let p         = symbol_start_pos () in\n";
  output_string file "   let file_name = p.Lexing.pos_fname  in\n";
  output_string file "   let line_num  = p.Lexing.pos_lnum   in\n";
  output_string file "   let col_num   = (p.Lexing.pos_cnum-p.Lexing.pos_bol+1) in\n";
  output_string file "   Pos(file_name,line_num,col_num)\n";
  output_string file ";;\n";
  output_string file "\n";
  output_string file "(* gets a pos data structure from a lexing position *)\n";
  output_string file "let get_pos (p : Lexing.position) =\n";
  output_string file "   let file_name = p.Lexing.pos_fname in\n";
  output_string file "   let line_num  = p.Lexing.pos_lnum  in\n";
  output_string file "   let col_num   = (p.Lexing.pos_cnum-p.Lexing.pos_bol+1) in\n";
  output_string file "   Pos(file_name,line_num,col_num)\n";
  output_string file ";;\n";
  output_string file "\n";
  output_string file "(* updates the lexer position to the next line\n";
  output_string file " * (this is used since we skip newlines in the\n";
  output_string file " *  lexer, but we still wish to remember them\n";
  output_string file " *  for proper line positions) *)\n";
  output_string file "let do_newline lb = \n";
  output_string file "   Lexing.new_line lb\n";
  output_string file ";;\n";
  output_string file "\n";
  output_string file "(* dies with a system error s *)\n";
  output_string file "let die_system_error (s : string) =\n";
  output_string file "   print_string s;\n";
  output_string file "   print_string \"\\n\";\n";
  output_string file "   exit 1\n";
  output_string file ";;\n";
  output_string file "\n";
  output_string file "let rec count_newlines s lb = match s with\n";
  output_string file "  | \"\" -> 0\n";
  output_string file "  | _  -> let c = String.sub s 0 1 in\n";
  output_string file "          let cs = String.sub s 1 ((String.length s)-1) in\n";
  output_string file "          if (c=\"\\n\") then (do_newline lb; 1+(count_newlines cs lb))\n";
  output_string file "                      else (count_newlines cs lb)\n";
  output_string file ";;\n";
  (match footer with
  | None -> ()
  | Some(Code(_,s)) -> output_string file ("\n"^s));
;;

let generate_skeleton_makefile file prefix =
   let out_file = get_out_file () in
   generate_makefile_vars file;
   output_string file "\n";
   output_string file "LIBS =";
   Hashtbl.iter (fun k v ->
      output_string file (" "^k^".$(CMA)")
   ) libs;
   output_string file "\n\n";
   output_string file (out_file^":\tflags.$(CMO) "^prefix^"utils.$(CMO) "^prefix^"ast.$(CMO) "^
                      prefix^"parser.$(CMO) "^prefix^"lexer.$(CMO) "^prefix^"main.$(CMO) main.$(CMO)\n");
   output_string file ("\t$(OCAMLC) -o "^out_file^" $(LIBS) flags.$(CMO) "^prefix^"utils.$(CMO) "^
                      prefix^"ast.$(CMO) "^prefix^"parser.$(CMO) "^prefix^"lexer.$(CMO) "^
                      prefix^"main.$(CMO) main.$(CMO)\n");
   output_string file "\n";
   output_string file ("main.$(CMO):\tmain.ml "^prefix^"main.$(CMO) "^prefix^"parser.$(CMO) "^
                      prefix^"lexer.$(CMO) "^
                      prefix^"ast.$(CMO) "^prefix^"utils.$(CMO) flags.$(CMO)\n");
   output_string file "\t$(OCAMLC) -c main.ml\n";
   output_string file "\n";
   output_string file "flags.$(CMO):\tflags.ml\n";
   output_string file "\t$(OCAMLC) -c flags.ml\n";
   output_string file "\n";
   output_string file (prefix^"Makefile:\t"^(!filename)^"\n");
   output_string file ("\tpgg "^(!filename)^"\n");
   output_string file "\n";
   output_string file ("clean:\t"^prefix^"clean\n");
   output_string file ("\trm -rf *.o *.cm* *.mli "^prefix^"main.ml "^prefix^"utils.ml "^
                      prefix^"ast.ml "^
                      prefix^"parser.ml "^prefix^"parser.mly "^prefix^"lexer.ml "^
                      prefix^"lexer.mll "^prefix^"Makefile\n");
   output_string file "\n";
   output_string file ("include "^(get_prefix ())^"Makefile\n")
;;

let generate_skeleton_main file prefix =
   let import = String.capitalize prefix in
   output_string file ("open "^import^"main;;\n");
   output_string file ("open Flags;;\n");
   output_string file "\n";
   output_string file "let i = parse_command_line () in\n";
   output_string file "let result = get_ast i in\n";
   output_string file "(* Ast.print_grammar 0 result;\n";
   output_string file "print_newline(); *)\n";
   output_string file "exit 0;;\n";
;;

let generate_skeleton_flags file prefix =
   let out_file = get_out_file () in
   output_string file "(* flag defaults *)\n";
   output_string file "let filename = ref \"\";; (* TODO - this will always be set *)\n";
   output_string file "let out_file = ref (None : string option)\n";
   output_string file "\n";
   output_string file ("let banner_text = \"Welcome to "^out_file^" v. 1.0\";;\n");
   output_string file "let usage_msg = banner_text^\"\\n\"^\n";
   output_string file ("                \"Usage: "^out_file^" [options] <file>\";;\n");
   output_string file "\n";
   output_string file "(* parse the command-line arguments *)\n";
   output_string file "let args = Arg.align [\n";
   output_string file "   (\"-o\",        Arg.String(fun x -> out_file := Some(x)),\n";
   output_string file "                    \"<file> Location for the result\");\n";
   output_string file "];;\n";
   output_string file "\n";
   output_string file "let error_usage_msg () =\n";
   output_string file "   Arg.usage args usage_msg;\n";
   output_string file "   exit 1\n";
   output_string file ";;\n";
   output_string file "\n";
   output_string file "(* dies with a system error s *)\n";
   output_string file "let die_system_error (s : string) =\n";
   output_string file "   print_string s;\n";
   output_string file "   print_string \"\\n\";\n";
   output_string file "   exit 1\n";
   output_string file ";;\n";
   output_string file "\n";
   output_string file "let parse_command_line () : in_channel =\n";
   output_string file "   let f_set = ref false in\n";
   output_string file "   Arg.parse args (fun x -> f_set := true; filename := x) banner_text;\n";
   output_string file "   (* use the command-line filename if one exists, otherwise use stdin *)\n";
   output_string file "   match !f_set with\n";
   output_string file "   | false -> error_usage_msg ()\n";
   output_string file "   | true -> (\n";
   output_string file "      try (open_in !filename)\n";
   output_string file "      with _ -> die_system_error (\"can't read from file: \"^(!filename))\n";
   output_string file "   )\n";
   output_string file ";;\n";
;;

let generate_skeleton () =
   let prefix = get_prefix () in
   let dir = (!out_dir)^(Filename.dir_sep) in
   let makefile_path = dir^"Makefile" in
   if not (Sys.file_exists makefile_path) then (
      let file = create_file makefile_path in
      generate_skeleton_makefile file prefix;
      close_out file
   );
   let main_path = dir^"main.ml" in
   if not (Sys.file_exists main_path) then (
      let file = create_file main_path in
      generate_skeleton_main file prefix;
      close_out file
   );
   let flags_path = dir^"flags.ml" in
   if not (Sys.file_exists flags_path) then (
      let file = create_file flags_path in
      generate_skeleton_flags file prefix;
      close_out file
   );
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
  (*let name   = get_filename !filename in*)
  let prefix = get_prefix () in
  let prefix_up = String.capitalize prefix in
  let dir    = (!out_dir)^(Filename.dir_sep) in
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
    generate_utils_code file_utils g;
    close_out file_utils;
    print_string "done.\n";
    let h = ((SubpatternHashtbl.create 100) :
       (string*((string*int) option)*string option*pos) SubpatternHashtbl.t) in (* TODO - size? *)
    get_terminals_grammar g h;
    let file_parser = create_file (dir^prefix^"parser.mly") in
    (* write the parser.mly contents *)
    generate_parser_code file_parser prefix_up g h;
    close_out file_parser;
    print_string "done.\n";
    let file_lexer  = create_file (dir^prefix^"lexer.mll" ) in
    (* write the lexer.mll contents *)
    generate_lexer_code file_lexer prefix_up g h;
    close_out file_lexer;
    print_string "done.\n";
    let file_main   = create_file (dir^prefix^"main.ml"   ) in
    (* write the main.ml contents *)
    generate_main_code file_main prefix_up g;
    close_out file_main;
    print_string "done.\n"
;;
