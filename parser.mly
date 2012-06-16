/* File parser.mly */
%{
   open Ast;;
   open Utils;;

   type opt = OprOption of op
            | PrecOption of int
            | AssocOption of assoc
            | SuppOption of bool
   ;;
%}
%token <int> INT
%token <string> IDENT
%token <Lexing.position*string> CODE
%token <string> STRINGQUOT 
%token <string> CHARSET
%token <char> CHARQUOT
%token PLUS MINUS TIMES DIV
%token LPAREN RPAREN
%token EOL
%token RANGE
%token EOF
%token COLON SEMI LBRACK RBRACK
%token LEFT RIGHT UNARY
%token ARROW BAR DQUOT QUOT STAR PLUS QUESTION SUPP WILDCARD DIFF ENDFILE
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
         Grammar(p,$1,$4,$2::$3)
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
   IDENT ARROW pattern pattern_bar_list SEMI { Production(get_current_pos (),$1,$3::$4) }
;

pattern_bar_list:
                              { [] }
   | BAR pattern pattern_bar_list { $2::$3 } 
;

pattern:
   subpattern subpattern_list label code_block { Pattern(get_current_pos (),$1::$2,$3,$4) }
;

label:
                 { None }
   | COLON IDENT { Some($2) }
;

subpattern_list:
                                { [] }
   | subpattern subpattern_list { $1::$2 }
;

subpattern:
     atom opts             { SimpleSubpattern(get_current_pos (),$1,$2) }
   | atom RANGE atom opts  { RangeSubpattern(get_current_pos (),$1,$3,$4) }
   | LPAREN CODE RPAREN    { let (p,s) = $2 in
                             let p2 = get_pos p in
                             CodeSubpattern(p2,Code(p2,s)) }
;

atom:
     ENDFILE    { EOFAtom(get_current_pos ()) }
   | IDENT      { IdentAtom(get_current_pos (),$1) }
   | STRINGQUOT { StringAtom(get_current_pos (),$1) }
   | charsets   { CharsetsAtom(get_current_pos(),$1) }
   | LPAREN subpatterns subpatterns_bar_list RPAREN {
      ChoiceAtom(get_current_pos (),$2::$3) } 
;

subpatterns_bar_list:
                                     { [] }
   | BAR subpatterns subpatterns_bar_list { $2::$3 }
;

subpatterns:
     subpattern subpattern_list { Subpatterns(get_current_pos (),$1::$2) }

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
      let (opr,pri,assoc,supp) = List.fold_left (fun (opr,pri,assoc,supp) o ->
         match (o,opr,pri,assoc,supp) with
         | (OprOption(op),None,_,_,_) -> (Some(op),pri,assoc,supp)
         | (PrecOption(i),_,None,_,_) -> (opr,Some(i),assoc,supp)
         | (AssocOption(a),_,_,None,_) -> (opr,pri,Some(a),supp)
         | (SuppOption(b),_,_,_,None) -> (opr,pri,assoc,Some(b))
         | _ -> parse_error "multiple modifiers of same type in options list"
      ) (None,None,None,None) l in
      let sf = (match supp with
      | None -> false
      | _ -> true) in
      Options(p,opr,pri,assoc,sf)
   }
;

opt_list:
                  { [] }
   | opt opt_list { $1::$2 }
;

opt:
   | op_opr   { OprOption($1) }
   | op_prec  { PrecOption($1) }
   | op_assoc { AssocOption($1) }
   | op_supp  { SuppOption($1) }
   
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

op_supp:
   | SUPP { true }
;
