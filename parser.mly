/* File parser.mly */
%{
   open Ast;;
   open Utils;;

   type opt = OprOption of op
            | PrecOption of int
            | AssocOption of assoc
            | SuppPrintOption of bool
            | TypeOption of (typ * code option)
   ;;

%}
%token <int> INT
%token <string> IDENT
%token <Lexing.position*string> CODE
%token <string> STRINGQUOT TYPENAME
%token <string> CHARSET
%token <char> CHARQUOT
%token PLUS MINUS TIMES DIV
%token LPAREN RPAREN
%token LANGLE RANGLE
%token EOL
%token RANGE
%token EOF
%token COLON SEMI LBRACK RBRACK
%token LEFT RIGHT UNARY
%token ARROW BAR DQUOT QUOT STAR PLUS QUESTION SUPPPRINT WILDCARD DIFF ENDFILE
%left PLUS MINUS /* lowest precedence */
%left TIMES DIV /* medium precedence */
%nonassoc UMINUS /* highest precedence */
%start main /* the entry point */
%type <Ast.grammar> main
%%
main:
   code_block production prod_list code_block EOF {
      let p = (match $1 with
      | None -> get_pos (rhs_start_pos 2)
      | Some(Code(p,_)) -> p) in
         Grammar(p,$1,$4,$2,$3)
   }
;

code_block:
          { None }             /* TODO - delete NoPos */
   | CODE { let (p,s) = $1 in Some(Code(get_pos p,s)) }

prod_list:
                          { [] }
   | production prod_list { $1::$2 }
;

production:
   IDENT ARROW pattern pattern_bar_list SEMI { Production(get_current_pos (),$1,$3,$4) }
;

pattern_bar_list:
                              { [] }
   | BAR pattern pattern_bar_list { $2::$3 } 
;

pattern:
   subpattern_list eof_op label code_block {
      let (l,(pr,assoc)) = $3 in Pattern(get_current_pos (),$1,l,$2,$4,pr,assoc)
   }
;

eof_op:
   |         { false }
   | ENDFILE { true }
;

label:
                 { (None,(None,None)) }
   | COLON IDENT pattern_opts { (Some(Type(get_current_pos (), $2)),$3) }
   | COLON       pattern_opts { (Some(EmptyType(get_current_pos ())),$2) }
;

pattern_opts:
   pattern_opt_list {
      let l = $1 in
      let (pri,assoc) =
      List.fold_left (fun (pri,assoc) o ->
         match (o,pri,assoc) with
         | (PrecOption(i),None,_) -> (Some(i),assoc)
         | (AssocOption(a),_,None) -> (pri,Some(a))
         | _ -> parse_error "malformed rule associativity/precedence"
      ) (None,None) l in
      (pri,assoc)
   }
;

pattern_opt_list:
                                  { [] }
   | pattern_opt pattern_opt_list { $1::$2 }
;

pattern_opt:
   | op_prec       { PrecOption($1) }
   | op_assoc      { AssocOption($1) }
   
;

subpattern_list:
                                { [] }
   | subpattern subpattern_list { $1::$2 }
;

subpattern:
     atom opts             { let msg = "only flat expressions may have precedence/associativity modifiers" in
                             if (not (is_atom_flat $1)) then (
                             match $2 with
                             | Options(ps,_,Some(i),_,_,_,_) -> die_error ps msg
                             | Options(ps,_,_,Some(a),_,_,_) -> die_error ps msg
                             | _ -> ());
                             SimpleSubpattern(get_current_pos (),$1,$2) }
   | atom RANGE atom opts  { let msg = "range expressions cannot contain identifiers" in
                             if (not (is_atom_flat $1)) then (
                                die_error (get_atom_pos $1) msg
                             );
                             if (not (is_atom_flat $3)) then (
                                die_error (get_atom_pos $3) msg
                             );
                             RangeSubpattern(get_current_pos (),$1,$3,$4) }
   | LPAREN CODE RPAREN    { let (p,s) = $2 in
                             let p2 = get_pos p in
                             CodeSubpattern(p2,Code(p2,s)) }
;

atom:
   | IDENT      { IdentAtom(get_current_pos (),$1) }
   | STRINGQUOT { StringAtom(get_current_pos (),$1) }
   | charsets   { CharsetsAtom(get_current_pos(),$1) }
   | LPAREN subpatterns subpatterns_bar_list RPAREN {
      ChoiceAtom(get_current_pos (),$2,$3) } 
;

subpatterns_bar_list:
                                     { [] }
   | BAR subpatterns subpatterns_bar_list { $2::$3 }
;

subpatterns:
     subpattern subpattern_list {
        let ok = List.fold_left (fun res s ->
           if res then res
           else (not (is_subpattern_empty s))
        ) false ($1::$2) in
        if (not ok) then parse_error "empty subpattern list";
        Subpatterns(get_current_pos (),$1, $2) 
     }

charsets:
     charset              { SingletonCharsets(get_current_pos (),$1) } 
   | charset DIFF charset { DiffCharsets(get_current_pos (),$1,$3) } 

charset:
     WILDCARD { WildcardCharset(get_current_pos ()) }
   | CHARQUOT { SingletonCharset(get_current_pos (),$1) }
   | CHARSET  { let (l,b) = Ast.compile_charset $1 in
                ListCharset(get_current_pos (),l,b) }

opts:
   opt_list {
      let p = get_current_pos () in
      let l = $1 in
      let (opr,pri,assoc,supp_print,ty,cd) =
      List.fold_left (fun (opr,pri,assoc,supp_print,ty,cd) o ->
         match (o,opr,pri,assoc,supp_print,ty,cd) with
         | (OprOption(op),None,_,_,_,_,_) -> (Some(op),pri,assoc,supp_print,ty,cd)
         | (PrecOption(i),_,None,_,_,_,_) -> (opr,Some(i),assoc,supp_print,ty,cd)
         | (AssocOption(a),_,_,None,_,_,_) -> (opr,pri,Some(a),supp_print,ty,cd)
         | (SuppPrintOption(b),_,_,_,None,_,_) -> (opr,pri,assoc,Some(b),ty,cd)
         | (TypeOption((ty,cd)),_,_,_,_,None,_) -> (opr,pri,assoc,supp_print,Some(ty),cd)
         | _ -> parse_error "multiple modifiers of same type in options list"
      ) (None,None,None,None,None,None) l in
      let sp = (match supp_print with
      | None -> false
      | _ -> true) in
      Options(p,opr,pri,assoc,sp,ty,cd)
   }
;

opt_list:
                  { [] }
   | opt opt_list { $1::$2 }
;

opt:
   | op_opr        { OprOption($1) }
   | op_prec       { PrecOption($1) }
   | op_assoc      { AssocOption($1) }
   | op_supp_print { SuppPrintOption($1) }
   | op_type       { TypeOption($1) }
   
;

op_opr:
   | STAR     { StarOp(get_current_pos ()) }
   | PLUS     { PlusOp(get_current_pos ()) }
   | QUESTION { QuestionOp(get_current_pos ()) }
;

op_prec:
   | INT { $1 }
;

op_assoc:
   | LEFT  { LeftAssoc(get_current_pos ()) }
   | RIGHT { RightAssoc(get_current_pos ()) }
   | UNARY { UnaryAssoc(get_current_pos ()) }
;

op_supp_print:
   | SUPPPRINT { true }
;

op_type:
   | LANGLE code_block RANGLE       { match $2 with
                                      | None -> (EmptyType(get_current_pos ()),None)
                                      | Some(Code(_,s)) -> (parse_type (get_current_pos ()) s, None)
                                    }
   | LANGLE code_block COLON code_block RANGLE {
      match $4 with
      | None -> (EmptyType(get_current_pos ()),$2)
      | Some(Code(p,s)) -> ((parse_type p s),$2)
   }
;
