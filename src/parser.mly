/* File parser.mly */
%{
   open Ast;;
   open Utils;;

   type opt = OprOption of op
            | PrecOption of int
            | AssocOption of assoc
            | TypeOption of (typ * code option)
            | PrintOption of code
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
%token RECUR
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
   | subpattern subpattern_list               { $1::$2 }
;

subpattern:
     atom opts             { let msg = "only flat expressions may have precedence/associativity modifiers" in
                             if (not (is_atom_flat $1)) then (
                             match $2 with
                             | Options(ps,_,Some(i),_,_,_,_) -> die_error ps msg
                             | Options(ps,_,_,Some(a),_,_,_) -> die_error ps msg
                             | _ -> ());
                             SimpleSubpattern(get_current_pos (),$1,$2) }
   | quot RECUR quot opts  { RecursiveSubpattern(get_current_pos (),$1,$3,$4) }
;

quot:
   | CHARQUOT   { String.make 1 $1 }
   | STRINGQUOT { $1 }
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
   | subpattern subpattern_list { Subpatterns(get_current_pos (),$1,$2) }

charsets:
     charset              { SimpleCharsets(get_current_pos (),$1) } 
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
      let (opr,pri,assoc,ty,cd,cp) =
      List.fold_left (fun (opr,pri,assoc,ty,cd,cp) o ->
         match (o,opr,pri,assoc,ty,cd,cp) with
         | (OprOption(op),None,_,_,_,_,_) -> (Some(op),pri,assoc,ty,cd,cp)
         | (PrecOption(i),_,None,_,_,_,_) -> (opr,Some(i),assoc,ty,cd,cp)
         | (AssocOption(a),_,_,None,_,_,_) -> (opr,pri,Some(a),ty,cd,cp)
         | (TypeOption((ty,cd)),_,_,_,None,_,_) -> (opr,pri,assoc,Some(ty),cd,cp)
         | (PrintOption(c),_,_,_,_,_,None) -> (opr,pri,assoc,ty,cd,Some(c))
         | _ -> parse_error "multiple modifiers of same type in options list"
      ) (None,None,None,None,None,None) l in
      Options(p,opr,pri,assoc,ty,cd,cp)
   }
;

opt_list:
                  { [] }
   | opt opt_list { $1::$2 }
;

opt:
   | op_opr         { OprOption($1) }
   | op_prec        { PrecOption($1) }
   | op_assoc       { AssocOption($1) }
   | op_type        { TypeOption($1) }
   | SUPPPRINT CODE { let (p,s) = $2 in PrintOption(Code(get_pos p,s)) }
   
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
