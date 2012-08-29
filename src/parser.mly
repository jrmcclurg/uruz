/* File parser.mly */
%{
   open Ast;;
   open Utils;;

   type opt = OprOption of op
            | PrecOption of int
            | AssocOption of assoc
            | CodeOption of code
            | TypeOption of typ
            | PrintOption of code
            | EqOption of code
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
%token ARROW BAR DQUOT QUOT STAR PLUS QUESTION AMP EQUAL DOLLAR WILDCARD DIFF ENDFILE
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
     atom opts { (* TODO - does this error work? *)
                             let msg = "only flat expressions may have precedence/associativity modifiers" in
                             if (not (is_atom_flat $1)) then (
                             match $2 with
                             | Options(ps,_,Some(i),_,_,_,_,_) -> die_error ps msg
                             | Options(ps,_,_,Some(a),_,_,_,_) -> die_error ps msg
                             | _ -> ());
                             SimpleSubpattern(get_current_pos (),$1,$2) }
   | quot RECUR quot opts { RecursiveSubpattern(get_current_pos (),$1,$3,$4) }
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
   | op_opr {
      Options(get_current_pos (),$1,None,None,None,None,None,None) }
   | op_opr LANGLE opt_list RANGLE {
      let p = get_current_pos () in
      let l = $3 in
      let (pri,assoc,ty,cd,cp,eq) =
      List.fold_left (fun (pri,assoc,ty,cd,cp,eq) o ->
         match (o,pri,assoc,ty,cd,cp,eq) with
         | (PrecOption(i),None,_,_,_,_,_) -> (Some(i),assoc,ty,cd,cp,eq)
         | (AssocOption(a),_,None,_,_,_,_) -> (pri,Some(a),ty,cd,cp,eq)
         | (TypeOption(ty),_,_,None,_,_,_) -> (pri,assoc,Some(ty),cd,cp,eq)
         | (CodeOption(cd),_,_,_,None,_,_) -> (pri,assoc,ty,Some(cd),cp,eq)
         | (PrintOption(c),_,_,_,_,None,_) -> (pri,assoc,ty,cd,Some(c),eq)
         | (EqOption(c),_,_,_,_,_,None) -> (pri,assoc,ty,cd,cp,Some(c))
         | _ -> parse_error "multiple modifiers of same type in options list"
      ) (None,None,None,None,None,None) l in
      Options(p,$1,pri,assoc,ty,cd,cp,eq)
   }
;

opt_list:
                  { [] }
   | opt opt_list { $1::$2 }
;

opt:
   | op_prec        { PrecOption($1) }
   | op_assoc       { AssocOption($1) }
   | CODE           { let (p,s) = $1 in CodeOption(Code(get_pos p,s)) }
   | COLON CODE     { let (p,s) = $2 in TypeOption(parse_type (get_pos p) s) }
   | AMP CODE       { let (p,s) = $2 in PrintOption(Code(get_pos p,s)) }
   | EQUAL CODE     { let (p,s) = $2 in EqOption(Code(get_pos p,s)) }
   
;

op_opr:
   |          { None }
   | STAR     { Some(StarOp(get_current_pos ())) }
   | PLUS     { Some(PlusOp(get_current_pos ())) }
   | QUESTION { Some(QuestionOp(get_current_pos ())) }
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
   | LANGLE CODE RANGLE       { let (p,s) = $2 in
                                      (Some(parse_type (get_pos p) s), None)
                                    }
   | LANGLE CODE COLON code_block RANGLE {
      let (p,s) = $2 in
      let c = Some(Code(get_pos p,s)) in
      match $4 with
      | None -> (None,c)
      | Some(Code(p,s)) -> (Some(parse_type p s),c)
   }
;
