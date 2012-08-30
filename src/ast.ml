(*
 * Parser Generator Generator (PGG)
 * by Jedidiah R. McClurg
 * Department of EECS
 * Northwestern University
 * http://www.jrmcclurg.com/
 *
 * Copyright © 2012 Jedidiah R. McClurg
 * Distributed under the terms of the
 * GNU General Public License
 *)

(** Abstract Syntax Tree (AST) functionality *)
open Utils;;

(** {b AST data structures} *)

(** AST node for a grammar file *)
type grammar = Grammar of pos * code option * code option * production * production list (**
                Grammar file having given
                pos,
                header OCaml code,
                trailer OCaml code,
                first production, 
                successive productions *)

(** AST node for a production *)
and production = Production of pos * string * pattern * pattern list (**
                   Production having given
                   position,
                   name,
                   first pattern,
                   successive patterns *)

(** AST node for a pattern *)
and pattern = Pattern of pos * subpattern list * typ option * bool * code * int option * assoc option (**
                Pattern having given
                position,
                subpatterns,
                type,
                EOF flag,
                OCaml code,
                precedence,
                associativity *)

(** AST node for a subpattern *)
and subpattern = SimpleSubpattern of pos * atom * opts (**
                   Atomic subpattern having given
                   position,
                   atom,
                   options *)
               | RecursiveSubpattern of pos * string * string * opts (**
                  Recursive subpattern having given
                  position,
                  prefix,
                  suffix,
                  options *)

(** AST node for an atom *)
and atom = IdentAtom of pos * string (**
            Identifier atom having given
            position,
            name *)
         | StringAtom of pos * string (**
            String atom having given
            position,
            text *)
         | CharsetsAtom of pos * charsets (**
            Charsets atom having given
            position,
            charsets *)
         | ChoiceAtom of pos * subpatterns * subpatterns list (**
            Choice atom having given
            position,
            first collection of subpatterns,
            additional collections of subpatterns *)

(** AST node for subpatterns *)
and subpatterns = Subpatterns of pos * subpattern * subpattern list (**
                   Subpatterns having given
                   position,
                   first subpattern,
                   sucessive subpatterns *)

(** AST node for charsets *)
and charsets = SimpleCharsets of pos * charset (**
                Simple charsets having given
                position,
                charset *)
             | DiffCharsets of pos * charset * charset (**
                Difference charsets having given
                position,
                first charset,
                second charset *)

(** AST node for a charset *)
and charset = WildcardCharset of pos (**
               Wildcard charset having given
               position *)
            | SingletonCharset of pos * char (**
               Singleton charset having given
               position,
               character *)
            | ListCharset of pos * chars list * bool (**
               List charset having given
               position,
               characters,
               flag for inversion *)

(** AST node for chars *)
and chars = SingletonChars of pos * char (**
             Singleton chars having given
             position,
             character *)
          | RangeChars of pos * char * char (**
             Range chars having given
             position,
             beginning char,
             ending char *)

(** AST node for options *)
and opts = Options of pos * op option * int option * assoc option * typ option * code option * code option * code option(**
            Options having given
            position,
            operator,
            precedence,
            associativity,
            type,
            OCaml code for lexer,
            OCaml code for pretty-print,
            OCaml code for equality testing *)

(** AST node for operator *)
and op = StarOp of pos (**
          Star operator having given
          position *)
       | PlusOp of pos (**
          Plus operator having given
          position *)
       | QuestionOp of pos (**
          Question operator having given
          position *)

(** AST node for associativity *)
and assoc = LeftAssoc of pos (**
             Left associativity having given
             position *)
          | RightAssoc of pos (**
             Right associativity having given
             position *)
          | UnaryAssoc of pos (**
             Unary (no) associativity having given
             position *)

(** AST node for type *)
and typ = EmptyType of pos (**
           Empty type having given
           position *)
        | Type of pos * string (**
           Type having given
           position,
           name *)

(** AST node for code *)
and code = Code of pos * string (**
            Code block having given
            position, 
            OCaml code *)
;;

(** {b Functions for normalizing position} *)

(** Removes position from grammar:
    [reloc_grammar g]
    @param g the grammar to normalize *)
let rec reloc_grammar (g : grammar) =
   match g with
   | Grammar(p,c1,c2,pr,prl) -> Grammar(NoPos,reloc_code_opt c1,reloc_code_opt c2,
                                        reloc_production pr,List.map (fun p -> reloc_production p) prl)

(** Removes position from code:
    [reloc_code c]
    @param c the code to normalize *)
and reloc_code (c : code) =
   match c with
   | Code(p,s) -> Code(NoPos,s)

and reloc_code_opt (c : code option) =
   match c with
   | None -> None
   | Some(co) -> Some(reloc_code co)

and reloc_production (p : production) =
   match p with
   | Production(p,s,pa,pal) -> Production(NoPos,s,reloc_pattern pa,List.map (fun pa -> reloc_pattern pa) pal)

and reloc_pattern (p : pattern) = 
   match p with
   | Pattern(p,sl,t,b,c,i,asc) ->
      Pattern(NoPos,List.map (fun s -> reloc_subpattern s) sl,reloc_typ_opt t,b,reloc_code c,i,reloc_assoc_opt asc)

and reloc_subpattern (s : subpattern) =
   match s with
   | SimpleSubpattern(p,a,o) -> SimpleSubpattern(NoPos,reloc_atom a,reloc_opts o)
   | RecursiveSubpattern(p,a1,a2,o) -> RecursiveSubpattern(NoPos,a1,a2,reloc_opts o)

and reloc_atom (a : atom) =
   match a with
   | IdentAtom(p,s) -> IdentAtom(NoPos,s)
   | StringAtom(p,s) -> StringAtom(NoPos,s)
   | CharsetsAtom(p,c) -> CharsetsAtom(NoPos,reloc_charsets c)
   | ChoiceAtom(p,s,sl) -> ChoiceAtom(NoPos,reloc_subpatterns s,List.map (fun s -> reloc_subpatterns s) sl)

and reloc_subpatterns (s : subpatterns) =
   match s with
   | Subpatterns(p,s,sl) -> Subpatterns(NoPos,reloc_subpattern s,List.map (fun s -> reloc_subpattern s) sl)

and reloc_charsets (c : charsets) =
   match c with
   | SimpleCharsets(p,c) -> SimpleCharsets(NoPos,reloc_charset c)
   | DiffCharsets(p,c1,c2) -> DiffCharsets(NoPos,reloc_charset c1,reloc_charset c2)

and reloc_charset (c : charset) =
   match c with
   | WildcardCharset(p) -> WildcardCharset(NoPos)
   | SingletonCharset(p,c) -> SingletonCharset(NoPos,c)
   | ListCharset(p,cl,b) -> ListCharset(NoPos,cl,b)

and reloc_chars (c : chars) =
   match c with
   | SingletonChars(p,c) -> SingletonChars(NoPos,c)
   | RangeChars(p,c1,c2) -> RangeChars(NoPos,c1,c2)

and reloc_opts (o : opts) = 
   match o with
   | Options(p,o,i,a,t,c,cp,eq) -> Options(NoPos,reloc_op_opt o,i,reloc_assoc_opt a,reloc_typ_opt t,reloc_code_opt c,reloc_code_opt cp,reloc_code_opt eq)

and reloc_op (o : op) =
   match o with
   | StarOp(p) -> StarOp(NoPos)
   | PlusOp(p) -> PlusOp(NoPos)
   | QuestionOp(p) -> QuestionOp(NoPos)

and reloc_op_opt (o : op option) =
   match o with
   | None -> None
   | Some(o) -> Some(reloc_op o)

and reloc_assoc (a : assoc) =
   match a with
   | LeftAssoc(p) -> LeftAssoc(NoPos)
   | RightAssoc(p) -> RightAssoc(NoPos)
   | UnaryAssoc(p) -> UnaryAssoc(NoPos)

and reloc_assoc_opt (a : assoc option) =
   match a with
   | None -> None
   | Some(s) -> Some(reloc_assoc s)

and reloc_typ (t : typ) =
   match t with
   | EmptyType(p) -> EmptyType(NoPos)
   | Type(p,s) -> Type(NoPos,s)

and reloc_typ_opt (t : typ option) =
   match t with
   | None -> None
   | Some(t) -> Some(reloc_typ t)
;;

(* TODO XXX - add functions such as get_grammar_pos and is_grammar_eq *)

(** {b Functions for pretty-printing AST nodes} *)

let rec print_grammar (n:int) (g:grammar) : unit =
   match g with
   | Grammar(p,c1,c2,p2,pl2) ->
      let pl = p2::pl2 in
      print_indent n "Grammar(\n";
      print_pos (n+1) p;
      print_string ",\n";
      (match c1 with
      | None -> print_indent (n+1) "None"
      | Some(c1) -> print_indent (n+1) "Some(\n"; print_code (n+2) c1; 
                    print_string "\n"; print_indent (n+1) ")" );
      print_string ",\n";
      (match c2 with
      | None -> print_indent (n+1) "None"
      | Some(c2) -> print_indent (n+1) "Some(\n"; print_code (n+2) c2;
                    print_string "\n"; print_indent (n+1) ")" );
      print_string ",\n";
      print_indent (n+1) "[\n";
      let _ = List.fold_left (fun flag pr -> 
         if flag then print_string ",\n";
         print_production (n+2) pr;
         true
      ) false pl in (); 
      print_string "\n";
      print_indent (n+1) "]\n";
      print_indent n ")";

and print_code (n:int) (c:code) : unit =
   match c with
   | Code(p,st) ->
      print_indent n "Code(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_str (n+1) st;
      print_string "\n";
      print_indent n ")";

and print_str (n:int) (s:string) : unit =
   print_indent n ("\""^(String.escaped s)^"\"")

and print_chr (n:int) (c:char) : unit =
   print_indent n ("'"^(Char.escaped c)^"'")

and print_bl (n:int) (b:bool) : unit =
   print_indent n (if b then "true" else "false")

and print_regex (n:int) (s:string) : unit =
   print_indent n ("["^(String.escaped s)^"]") (* TODO - maybe escape this? *)

and print_prec (n:int) (i:int option) : unit =
   match i with
   | None -> print_indent n "None"
   | Some(k) ->
      print_indent n "";
      print_int k

and print_pos (n:int) (p:pos) : unit =
   match p with
   | NoPos -> print_indent n "NoPos"
   | Pos(f,l,m) ->
      print_indent n "Pos(\"";
      print_string f;
      print_string "\",";
      print_int l;
      print_string ",";
      print_int m;
      print_string ")";

and print_production (n:int) (pr:production) : unit =
   match pr with
   | Production(p,name,p2,pl2) ->
      let pl = p2::pl2 in
      print_indent n "Production(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_str (n+1) name;
      print_string ",\n";
      print_indent (n+1) "[\n";
      let _ = List.fold_left (fun flag pa ->
         if flag then print_string ",\n";
         print_pattern (n+2) pa;
         true;
      ) false pl in ();
      print_string "\n";
      print_indent (n+1) "]\n";
      print_indent n ")";

and print_pattern (n:int) (pa:pattern) : unit =
   match pa with
   | Pattern(p,slx,label,eof,s,i,asc) ->
      let sl = slx in
      print_indent n "Pattern(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_indent (n+1) "[\n";
      let _ = List.fold_left (fun flag sp ->
         if flag then print_string ",\n";
         print_subpattern (n+2) sp;
         true;
      ) false sl in ();
      print_string "\n";
      print_indent (n+1) "],\n";
      (match label with
      | None -> print_indent (n+1) "None"
      | Some(lab) -> print_indent (n+1) "Some(\n"; print_typ (n+2) lab;
                     print_string "\n"; print_indent (n+1) ")" );
      print_string "\n";
      print_code (n+1) s;
      print_string ",\n";
      print_indent (n+1) (if eof then "true" else "false");
      print_string ",\n";
      (match i with
      | None -> print_indent (n+1) "None"
      | Some(i) -> print_indent (n+1) "Some("; print_int i; print_string ")");
      print_string ",\n";
      print_assoc (n+1) asc;
      print_string "\n";
      print_indent n ")";

and print_subpattern (n:int) (sp:subpattern) : unit =
   match sp with
   | SimpleSubpattern(p,a,o) ->
      print_indent n "SimpleSubpattern(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_atom (n+2) a;
      print_string ",\n";
      print_opts (n+1) o;
      print_string "\n";
      print_indent n ")";
   | RecursiveSubpattern(p,a1,a2,o) ->
      print_indent n "RecursiveSubpattern(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_indent (n+2) a1;
      print_string ",\n";
      print_indent (n+2) a2;
      print_string ",\n";
      print_opts (n+1) o;
      print_string "\n";
      print_indent n ")";

and print_atom (n:int) (a:atom) : unit =
   match a with
   | IdentAtom(p,s) ->
      print_indent n "IdentAtom(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_str (n+1) s;
      print_string "\n";
      print_indent n ")";
   | StringAtom(p,s) ->
      print_indent n "StringAtom(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_str (n+1) s;
      print_string "\n";
      print_indent n ")";
   | CharsetsAtom(p,c) ->
      print_indent n "CharsetsAtom(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_charsets (n+1) c;
      print_string "\n";
      print_indent n ")"
   | ChoiceAtom(p,s2,sl2) ->
      let sl = s2::sl2 in
      print_indent n "ChoiceAtom(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_indent (n+1) "[\n";
      let _ = List.fold_left (fun flag sp ->
         if flag then print_string ",\n";
         print_subpatterns (n+2) sp;
         true;
      ) false sl in ();
      print_string "\n";
      print_indent (n+1) "],\n";
      print_indent n ")"

and print_subpatterns (n:int) (s:subpatterns) : unit =
   match s with
   | Subpatterns(p,s2,sl2) ->
      let sl = s2::sl2 in
      print_indent n "Subpatterns(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_indent (n+1) "[\n";
      let _ = List.fold_left (fun flag sp ->
         if flag then print_string ",\n";
         print_subpattern (n+2) sp;
         true;
      ) false sl in ();
      print_string "\n";
      print_indent (n+1) "],\n";
      print_indent n ")"

and print_charsets (n:int) (cs:charsets) : unit =
   match cs with
   | SimpleCharsets(p,c) ->
      print_indent n "SimpleCharsets(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_charset (n+1) c;
      print_string "\n";
      print_indent n ")";
   | DiffCharsets(p,c1,c2) ->
      print_indent n "DiffCharsets(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_charset (n+1) c1;
      print_string ",\n";
      print_charset (n+1) c2;
      print_string "\n";
      print_indent n ")"

and print_charset (n:int) (c:charset) : unit =
   match c with
   | WildcardCharset(p) ->
      print_indent n "WildcardCharset(";
      print_pos 0 p;
      print_indent n ")";
   | SingletonCharset(p,c) ->
      print_indent n "SingletonCharset(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_chr (n+1) c;
      print_string "\n";
      print_indent n ")"
   | ListCharset(p,cl,b) ->
      print_indent n "ListCharset(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_indent (n+1) "[\n";
      let _ = List.fold_left (fun flag a ->
         if flag then print_string ",\n";
         print_chars (n+2) a;
         true;
      ) false cl in ();
      print_string "\n";
      print_indent (n+1) "],\n";
      print_bl (n+1) b;
      print_string "\n";
      print_indent n ")"

and print_chars (n:int) (crs:chars) : unit =
   match crs with
   | SingletonChars(p,c) ->
      print_indent n "SingletonChars(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_chr (n+1) c;
      print_string "\n";
      print_indent n ")";
   | RangeChars(p,c1,c2) ->
      print_indent n "RangeChars(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_chr (n+1) c1;
      print_string ",\n";
      print_chr (n+1) c2;
      print_string "\n";
      print_indent n ")"

and print_opts (n:int) (o1:opts) : unit =
   match o1 with
   | Options(p,o,i,a,typo,co,cpo,eqo) ->
      print_indent n "Options(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_op (n+1) o;
      print_string ",\n";
      print_prec (n+1) i;
      print_string ",\n";
      print_assoc (n+1) a;
      print_string ",\n";
      (match typo with
      | None -> print_indent (n+1) "None"
      | Some(typ) -> print_indent (n+1) "Some(\n"; print_typ (n+2) typ;
                     print_string "\n"; print_indent (n+1) ")");
      print_string ",\n";
      (match co with
      | None -> print_indent (n+1) "None"
      | Some(c) -> print_indent (n+1) "Some(\n"; print_code (n+2) c;
                     print_string "\n"; print_indent (n+1) ")");
      print_string ",\n";
      (match cpo with
      | None -> print_indent (n+1) "None"
      | Some(c) -> print_indent (n+1) "Some(\n"; print_code (n+2) c;
                     print_string "\n"; print_indent (n+1) ")");
      print_string ",\n";
      (match eqo with
      | None -> print_indent (n+1) "None"
      | Some(c) -> print_indent (n+1) "Some(\n"; print_code (n+2) c;
                     print_string "\n"; print_indent (n+1) ")");
      print_string "\n";
      print_indent n ")";

and print_op (n:int) (o:op option) : unit =
   match o with
   | None -> print_indent n "None";
   | Some(StarOp(p)) ->
      print_indent n "StarOp(";
      print_pos 0 p;
      print_string ")";
   | Some(PlusOp(p)) ->
      print_indent n "PlusOp(";
      print_pos 0 p;
      print_string ")";
   | Some(QuestionOp(p)) ->
      print_indent n "QuestionOp(";
      print_pos 0 p;
      print_string ")";

and print_assoc (n:int) (a:assoc option) : unit =
   match a with
   | None -> print_indent n "None"
   | Some(LeftAssoc(p)) ->
      print_indent n "LeftAssoc(";
      print_pos 0 p;
      print_string ")";
   | Some(RightAssoc(p)) ->
      print_indent n "RightAssoc(";
      print_pos 0 p;
      print_string ")";
   | Some(UnaryAssoc(p)) ->
      print_indent n "UnaryAssoc(";
      print_pos 0 p;
      print_string ")";

and print_typ (n:int) (ty:typ) : unit =
   match ty with
   | EmptyType(p) -> print_indent n "EmptyType("; print_pos 0 p; print_string ")"
   | Type(p,s) ->
      print_indent n "Type(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_str (n+1) s;
      print_string "\n";
      print_indent n ")";
;;

(** {b Functions for handling type info} *)

let get_production_type s =
   if (is_capitalized s) then ((to_type_case s)^"_t")
   else s 
;;

let output_production_type file s =
   output_string file (get_production_type s)
;;

let parse_type (p : pos) (s : string) : typ = 
   let sp = "[\r\n\t ]+" in
   let t = Str.global_replace (Str.regexp sp) " " s in
   let t2 = Str.global_replace (Str.regexp ("^"^sp)) "" t in
   let t3 = Str.global_replace (Str.regexp (sp^"$")) "" t2 in
   if t3 = "" then EmptyType(p) else Type(p,t3)
;;


let rec get_subpattern_default_type (sp : subpattern) : string =
   match sp with
   (* TODO XXX - i think this needs to take the operators into acount!!! *)
   | SimpleSubpattern(_,a,Options(_,None,_,_,_,_,_,_)) -> get_atom_default_type a
   | SimpleSubpattern(_,(IdentAtom(_,_) as a),Options(_,Some(StarOp(_)),_,_,_,_,_,_)) ->
      (get_atom_default_type a)^" list"
   | SimpleSubpattern(_,(IdentAtom(_,_) as a),Options(_,Some(PlusOp(_)),_,_,_,_,_,_)) ->
      let t = (get_atom_default_type a) in
      "("^t^" * "^t^" list)"
   | SimpleSubpattern(_,(IdentAtom(_,_) as a),Options(_,Some(QuestionOp(_)),_,_,_,_,_,_)) ->
      (get_atom_default_type a)^" option"
   | SimpleSubpattern(_,_,Options(_,Some(StarOp(_)),_,_,_,_,_,_)) -> "string"
   | SimpleSubpattern(_,_,Options(_,Some(PlusOp(_)),_,_,_,_,_,_)) -> "string"
   | SimpleSubpattern(_,_,Options(_,Some(QuestionOp(_)),_,_,_,_,_,_)) -> "string"
   | RecursiveSubpattern(_,_,_,_) -> "string"

and get_atom_default_type (a : atom) : string=
   match a with
   | IdentAtom(_,s) -> get_production_type s
   | StringAtom(_,s) -> (if (String.length s) = 1 then "char" else "string")
   | CharsetsAtom(_,_) -> "char"
   | ChoiceAtom(_,sp,spl) ->
      let all_chars = List.fold_left (fun all_chars (Subpatterns(_,sp,spl)) ->
         let all_chars2 = (if (not all_chars) then all_chars
         else if (List.length spl) = 0 then ((get_subpattern_default_type sp) = "char")
         else false) in
         all_chars2
      ) true (sp::spl) in
      (if all_chars then "char" else "string")
;;

(** {b Functions for checking structure of AST nodes} *)

let rec is_subpattern_flat (s : subpattern) : bool =
   let result = 
   (match s with
   | SimpleSubpattern(_,a1,_) -> is_atom_flat a1
   | RecursiveSubpattern(_,a1,a2,_) -> false (*(is_atom_flat a1) && (is_atom_flat a2)*)
   ) in
   result

and is_atom_flat (a : atom) : bool =
   match a with
   | IdentAtom(_,s) -> false
   | StringAtom(_,s) -> true
   | CharsetsAtom(_,cs) -> true
   | ChoiceAtom(_,sp,spl) ->
      List.fold_left (fun result sp ->
         if (not result) then false
         else if (is_subpatterns_flat sp) then true
         else false
      ) true (sp::spl)

and is_subpatterns_flat (sp : subpatterns) : bool =
   match sp with
   | Subpatterns(_,s,sl) ->
      List.fold_left (fun result s ->
         if (not result) then false
         else if (is_subpattern_flat s) then true
         else false
      ) true (s::sl)
;;

let is_code_empty (c : code) : bool =
   match c with
   | Code(p,s) ->
   is_string_empty s
;;

(** {b Functions for handling charsets} *)

let rec compile_char_list (cl: char list) : chars list = 
   let (hd,tl) = three_hd cl in
   match hd with
   | a::'-'::c::[] ->
      if (a > c) then parse_error "invalid range"; (* TODO - error *)
      (RangeChars(NoPos,a,c))::(compile_char_list tl)
   | a::b::c::[]   -> (SingletonChars(NoPos,a))::(compile_char_list (b::c::tl))
   | a::b::[]      -> (SingletonChars(NoPos,a))::(compile_char_list (b::tl))
   | a::[]         -> (SingletonChars(NoPos,a))::(compile_char_list (tl))
   | _             -> []
;;

(** Compiles an escaped string into a chars list.
    Returns [(c,inv)], i.e. list of chars and flag for inverted charsets
    @param s the escaped string to compile *)
let compile_charset (s:string) : chars list * bool =
   let l = string_explode s in
   match l with
   | '^'::cs -> (compile_char_list cs, true)
   | _       -> (compile_char_list l , false)
;;

let get_char_list (cl : chars list) : char list = 
   List.fold_left (fun r c ->
      r@
      (match c with
      | SingletonChars(_,c) -> [c]
      | RangeChars(_,c1,c2) -> get_chars c1 c2)
   ) [] cl
;;
