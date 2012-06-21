open Utils;;

type grammar = Grammar of pos * code option * code option * production * production list (* code,prods *)
 and code = Code of pos * string
 and production = Production of pos * string * pattern * pattern list (* name,patterns *)
 and pattern = Pattern of pos * subpattern list * typ option * bool * code option * int option * assoc option
                               (* subpatterns,code *)
 and subpattern = SimpleSubpattern of pos * atom * opts
                (* NOTE - the atoms in RangeSubpattern are required (by parser)
                 *        to be flat *)
                | RangeSubpattern of pos * atom * atom * opts
                | CodeSubpattern of pos * code
 and atom = IdentAtom of pos * string
          | StringAtom of pos * string
          | CharsetsAtom of pos * charsets
          | ChoiceAtom of pos * subpatterns * subpatterns list
 and subpatterns = Subpatterns of pos * subpattern * subpattern list
 and charsets = SingletonCharsets of pos * charset
              | DiffCharsets of pos * charset * charset
 and charset = WildcardCharset of pos
             | SingletonCharset of pos * char 
             | ListCharset of pos * chars list * bool
 and chars = SingletonChars of pos * char
           | RangeChars of pos * char * char
 and opts = Options of pos * op option * int option * assoc option * bool * typ option * code option
 and op = StarOp of pos
        | PlusOp of pos
        | QuestionOp of pos
 and assoc = LeftAssoc of pos
           | RightAssoc of pos
           | UnaryAssoc of pos
 and typ = EmptyType of pos
         | Type of pos * string
;;

let rec equal_grammar (g1 : grammar) (g2 : grammar) : bool =
   match (g1,g2) with
   | (Grammar(_,c1,c2,p,pl),Grammar(_,c1t,c2t,pt,plt)) ->
      if (List.length pl) <> (List.length plt) then false
      else ((equal_code_opt c1 c1t) && (equal_code_opt c2 c2t) && (equal_production p pt) && 
      (equal_production_list pl plt))

and equal_code (c1 : code) (c2 : code) : bool = 
   match (c1,c2) with
   | (Code(_,s1),Code(_,s2)) -> s1 = s2

and equal_code_opt (c1 : code option) (c2 : code option) : bool = 
   match (c1,c2) with
   | (None,None) -> true
   | (Some(c1),Some(c2)) -> equal_code c1 c2
   | _ -> false

and equal_production (p1 : production) (p2 : production) : bool =
   match (p1,p2) with
   | (Production(_,s,p,pl),Production(_,st,pt,plt)) ->
      if (List.length pl) <> (List.length plt) then false
      else ((s = st) && (equal_pattern p pt) && (equal_pattern_list pl plt))

and equal_production_list (pl : production list) (plt : production list) : bool =
      if (List.length pl) <> (List.length plt) then false
      else (
      List.fold_left2 (fun res p1 p2 ->
         if (not res) then res
         else equal_production p1 p2
      ) true pl plt)

and equal_pattern (p1 : pattern) (p2 : pattern) : bool =
   match (p1,p2) with
   | (Pattern(_,pl,t,b,c,i,asc),Pattern(_,plt,tt,bt,ct,it,asct)) ->
      if (List.length pl) <> (List.length plt) then false
      else ((equal_subpattern_list pl plt) &&
            (equal_typ_opt t tt) && (b = bt) && (equal_code_opt c ct) && (i = it) && (equal_assoc_opt asc asct))

and equal_pattern_list (pl : pattern list) (plt : pattern list) : bool =
      if (List.length pl) <> (List.length plt) then false
      else (
      List.fold_left2 (fun res p1 p2 ->
         if (not res) then res
         else equal_pattern p1 p2
      ) true pl plt)

and equal_subpattern (p1 : subpattern) (p2 : subpattern) : bool =
   match (p1,p2) with
   | (SimpleSubpattern(_,a,o),SimpleSubpattern(_,at,ot)) -> ((equal_atom a at) && (equal_opts o ot))
   | (RangeSubpattern(_,a1,a2,o),RangeSubpattern(_,a1t,a2t,ot)) ->
      ((equal_atom a1 a1t) && (equal_atom a2 a2t) && (equal_opts o ot))
   | (CodeSubpattern(_,c),CodeSubpattern(_,ct)) -> (equal_code c ct)
   | _ -> false

and equal_subpattern_list (pl : subpattern list) (plt : subpattern list) : bool =
      if (List.length pl) <> (List.length plt) then false
      else (
      List.fold_left2 (fun res p1 p2 ->
         if (not res) then res
         else equal_subpattern p1 p2
      ) true pl plt)

and equal_typ (c1 : typ) (c2 : typ) : bool = 
   match (c1,c2) with
   | (EmptyType(_),EmptyType(_)) -> true
   | (Type(_,s1),Type(_,s2)) -> s1 = s2
   | _ -> false

and equal_typ_opt (c1 : typ option) (c2 : typ option) : bool = 
   match (c1,c2) with
   | (None,None) -> true
   | (Some(c1),Some(c2)) -> equal_typ c1 c2
   | _ -> false

and equal_atom (a1 : atom) (a2 : atom) : bool =
   match (a1,a2) with
   | (IdentAtom(_,s1),IdentAtom(_,s2)) -> s1 = s2
   | (StringAtom(_,s1),StringAtom(_,s2)) -> s1 = s2
   | (CharsetsAtom(_,c1),CharsetsAtom(_,c2)) -> equal_charsets c1 c2
   | (ChoiceAtom(_,s,sl),ChoiceAtom(_,st,slt)) -> ((equal_subpatterns s st) && (equal_subpatterns_list sl slt))
   | _ -> false

and equal_opts (o1 : opts) (o2 : opts) : bool =
   match (o1,o2) with
   | (Options(_,o,i,a,b,t,c),Options(_,ot,it,at,bt,tt,ct)) ->
      ((equal_op_opt o ot) && (i = it) && (equal_assoc_opt a at) && (b = bt) && (equal_typ_opt t tt) && (equal_code_opt c ct))

and equal_charsets (c1 : charsets) (c2 : charsets) : bool =
   match (c1,c2) with
   | (SingletonCharsets(_,c),SingletonCharsets(_,ct)) -> equal_charset c ct
   | (DiffCharsets(_,c1,c2),DiffCharsets(_,c1t,c2t)) -> ((equal_charset c1 c1t) && (equal_charset c2 c2t))
   | _ -> false

and equal_subpatterns (c1 : subpatterns) (c2 : subpatterns) : bool =
   match (c1,c2) with
   | (Subpatterns(_,s,sl),Subpatterns(_,st,slt)) -> ((equal_subpattern s st) && (equal_subpattern_list sl slt))

and equal_subpatterns_list (pl : subpatterns list) (plt : subpatterns list) : bool =
      if (List.length pl) <> (List.length plt) then false
      else (
      List.fold_left2 (fun res p1 p2 ->
         if (not res) then res
         else equal_subpatterns p1 p2
      ) true pl plt)

and equal_op (o1 : op) (o2 : op) : bool = 
   match (o1,o2) with
   | (StarOp(_),StarOp(_)) -> true
   | (PlusOp(_),PlusOp(_)) -> true
   | (QuestionOp(_),QuestionOp(_)) -> true
   | _ -> false

and equal_op_opt (o1 : op option) (o2 : op option) : bool = 
   match (o1,o2) with
   | (None,None) -> true
   | (Some(o1),Some(o2)) -> equal_op o1 o2
   | _ -> false

and equal_assoc (o1 : assoc) (o2 : assoc) : bool = 
   match (o1,o2) with
   | (LeftAssoc(_),LeftAssoc(_)) -> true
   | (RightAssoc(_),RightAssoc(_)) -> true
   | (UnaryAssoc(_),UnaryAssoc(_)) -> true
   | _ -> false

and equal_assoc_opt (o1 : assoc option) (o2 : assoc option) : bool = 
   match (o1,o2) with
   | (None,None) -> true
   | (Some(a1),Some(a2)) -> equal_assoc a1 a2
   | _ -> false

and equal_charset (c1 : charset) (c2 : charset) : bool =
   match (c1,c2) with
   | (WildcardCharset(_),WildcardCharset(_)) -> true
   | (SingletonCharset(_,c1),SingletonCharset(_,c2)) -> (c1 = c2)
   | (ListCharset(_,c,b),ListCharset(_,ct,bt)) -> ((c = ct) && (b = bt))
   | _ -> false

;;

let rec reloc_grammar (g : grammar) =
   match g with
   | Grammar(p,c1,c2,pr,prl) -> Grammar(NoPos,reloc_code_opt c1,reloc_code_opt c2,
                                        reloc_production pr,List.map (fun p -> reloc_production p) prl)

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
      Pattern(NoPos,List.map (fun s -> reloc_subpattern s) sl,reloc_typ_opt t,b,reloc_code_opt c,i,reloc_assoc_opt asc)

and reloc_subpattern (s : subpattern) =
   match s with
   | SimpleSubpattern(p,a,o) -> SimpleSubpattern(NoPos,reloc_atom a,reloc_opts o)
   | RangeSubpattern(p,a1,a2,o) -> RangeSubpattern(NoPos,reloc_atom a1,reloc_atom a2,reloc_opts o)
   | CodeSubpattern(p,c) -> CodeSubpattern(NoPos,reloc_code c)

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
   | SingletonCharsets(p,c) -> SingletonCharsets(NoPos,reloc_charset c)
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
   | Options(p,o,i,a,b,t,c) -> Options(NoPos,reloc_op_opt o,i,reloc_assoc_opt a,b,reloc_typ_opt t,reloc_code_opt c)

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

(*print_string "ast.ml\n";;

let t1 = SimpleSubpattern(NoPos,StringAtom(NoPos,"+"),Options(NoPos,None,None,None,false,None)) ;;
let t2 = SimpleSubpattern(Pos("file",1,2),StringAtom(Pos("other",123,123),"+"),Options(NoPos,None,None,None,false,None)) ;;
if ((reloc_subpattern t1) = (reloc_subpattern t2)) then print_string "EQUAL!!!!\n";;
print_int (Hashtbl.hash (reloc_subpattern t1)); print_string "\n";;
print_int (Hashtbl.hash (reloc_subpattern t2)); print_string "\n";;*)

let rec string_explode (s:string) : char list =
   if (String.length s) > 0 then
      (String.get s 0)::(string_explode (String.sub s 1 ((String.length s)-1)))
   else
      []
;;

let three_hd (cl: char list) : char list * char list = 
   match cl with
   | a::b::c::l -> (a::b::c::[],l)
   | a::b::l    -> (a::b::[],l)
   | a::l       -> (a::[],l)
   | _          -> ([],cl)
;;

let rec compile_char_list (cl: char list) : chars list = 
   let (hd,tl) = three_hd cl in
   match hd with
   | a::'-'::c::[] -> (RangeChars(NoPos,a,c))::(compile_char_list tl)
   | a::b::c::[]   -> (SingletonChars(NoPos,a))::(compile_char_list (b::c::tl))
   | a::b::[]      -> (SingletonChars(NoPos,a))::(compile_char_list (b::tl))
   | a::[]         -> (SingletonChars(NoPos,a))::(compile_char_list (tl))
   | _             -> []
;;

let compile_charset (s:string) : chars list * bool =
   let l = string_explode s in
   match l with
   | '^'::cs -> (compile_char_list cs, true)
   | _       -> (compile_char_list l , false)
;;

let char_of_string (s:string) : char =
   let s2 = Str.global_replace (Str.regexp_string "\\[") "[" s in
   let s3 = Str.global_replace (Str.regexp_string "\\]") "]" s2 in
   Scanf.sscanf s3 "%C" (fun x -> x)
;;

let string_of_string (s:string) : string =
   let s2 = Str.global_replace (Str.regexp_string "\\[") "[" s in
   let s3 = Str.global_replace (Str.regexp_string "\\]") "]" s2 in
   Scanf.sscanf s3 "%S" (fun x -> x)
;;

let rec output_indent2 file n s =
   if n=0 then output_string file s
   else (output_string file " "; output_indent2 file (n-1) s)

and output_indent file n s =
   output_indent2 file (n*3) s

and print_indent n s =
   output_indent stdout n s

and output_spaces file n s =
   output_indent2 file n s
;;

let rec get_grammar_pos (g : grammar) : pos =
   match g with
   | Grammar(p,_,_,_,_) -> p

and get_atom_pos (a : atom) : pos =
   match a with
   | IdentAtom(p,_) -> p
   | StringAtom(p,_) -> p
   | CharsetsAtom(p,_) -> p
   | ChoiceAtom(p,_,_) -> p
;;

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
      (match s with
      | None -> print_indent (n+1) "None"
      | Some(s) -> print_indent (n+1) "Some(\n";
                   print_code (n+2) s; print_string "\n"; print_indent (n+1) ")" );
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
   | RangeSubpattern(p,a1,a2,o) ->
      print_indent n "RangeSubpattern(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_atom (n+2) a1;
      print_string ",\n";
      print_atom (n+2) a2;
      print_string ",\n";
      print_opts (n+1) o;
      print_string "\n";
      print_indent n ")";
   | CodeSubpattern(p,c) ->
      print_indent n "CodeSubpattern(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_code (n+2) c;
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
   | SingletonCharsets(p,c) ->
      print_indent n "SingletonCharsets(\n";
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
   | Options(p,o,i,a,sp,typo,co) ->
      print_indent n "Options(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_op (n+1) o;
      print_string ",\n";
      print_prec (n+1) i;
      print_string ",\n";
      print_assoc (n+1) a;
      print_string ",\n";
      print_indent (n+1) (if sp then "true" else "false");
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

let rec is_subpattern_flat (s : subpattern) : bool =
   let result = 
   (match s with
   | SimpleSubpattern(_,a1,_) -> is_atom_flat a1
   | RangeSubpattern(_,a1,a2,_) -> false (*(is_atom_flat a1) && (is_atom_flat a2)*)
   | CodeSubpattern(_,_) -> true) in
   print_string (if result then "true" else "false");
   print_string "\n";
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


let get_production_type s =
   if (is_capitalized s) then ((to_type_case s)^"_t")
   else s 
;;

let output_production_type file s =
   output_string file (get_production_type s)
;;

let rec get_subpattern_default_type (sp : subpattern) : string option =
   match sp with
   | SimpleSubpattern(_,a,_) -> get_atom_default_type a
   | RangeSubpattern(_,_,_,_) -> Some("string")
   | CodeSubpattern(_,_) -> None

and get_atom_default_type (a : atom) : string option =
   match a with
   | IdentAtom(_,s) -> Some(get_production_type s)
   | StringAtom(_,s) -> Some(if (String.length s) = 1 then "char" else "string")
   | CharsetsAtom(_,_) -> Some("char")
   | ChoiceAtom(_,sp,spl) ->
      let (all_chars,all_empty) = List.fold_left (fun (all_chars,all_empty) (Subpatterns(_,sp,spl)) ->
         let all_chars2 = (if (not all_chars) then all_chars
         else if (List.length spl) = 0 then ((get_subpattern_default_type sp) = Some("char"))
         else false) in
         let all_empty2 = (if (not all_empty) then all_empty
         else List.fold_left (fun res sp ->
            if (not res) then res
            else ((get_subpattern_default_type sp) = None)
         ) true (sp::spl)) in
         (all_chars2,all_empty2)
      ) (true,true) (sp::spl) in
      if all_empty then None else
      Some(if all_chars then "char" else "string")
;;

let rec is_pattern_empty (p : pattern) : bool = 
   match p with
   | Pattern(_,l,_,_,_,_,_) ->
   List.fold_left (fun res sp ->
      if (not res) then res
      else (is_subpattern_empty sp)
   ) true l

and is_subpattern_empty (s : subpattern) : bool =
   match (get_subpattern_default_type s) with
   | None -> true
   | _ -> false
;;
