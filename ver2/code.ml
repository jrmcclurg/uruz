(* TODO XXX - emit normalize_ and get_pos_ functions *)
(* TODO XXX - maybe disallow "_" in identifiers *)

(* TODO XXX

let explode s = List.rev (List.rev_map (fun s -> String.get s 0) (Str.split (Str.regexp "") s)) in
let x = explode "this is a test" in
Printf.printf "x = %s\n" (str_x_list (fun x -> String.make 1 x) x ", ");
let implode l = let str = String.create (List.length l) in let _ = List.fold_left (fun index c -> str.[index] <- c; index+1) 0 l in str in
let y = implode x in
Printf.printf "y = '%s'\n" y;

*)

open Uruz2_ast
open Uruz2_utils
open Flags

let rec is_finalized_typ (t : typ_t) : bool =
match t with
| SimpleType(_,AnyType(_)) -> false
| SimpleType(_,VarType(_)) -> false
(*| CompoundType(_,AbstrType(_,AnyName(_),cl)) -> false*)
| SimpleType(_,_) -> true
| CompoundType(_,CommaType(_,cll)) -> List.for_all (fun cl -> List.for_all is_finalized_constr_type cl) cll
| CompoundType(_,AbstrType(_,an,cl)) -> List.for_all is_finalized_constr_type cl

and is_finalized_constr_type (ct : constr_type_t) : bool =
match ct with
| SingletonConstrType(_,t) -> is_finalized_typ t
| InstConstrType(_,ct,_) -> is_finalized_constr_type ct

let rec range (a:int) (b:int) : int list = if (a > b) then [] else (a::(range (a+1) b))

let rev_flatten (l : 'a list list) : 'a list =
  List.fold_left (fun acc l2 ->
    List.rev_append l2 acc
  ) [] l

let tail_flatten (l : 'a list list) : 'a list =
  List.rev (rev_flatten l)

let opt_list_contains (ol : opt_t list) (kw : symb) (v : value_t) : (bool * opt_t list) =
  let ol2 = List.filter (fun x -> match x with ValOption(_,Some(k),v2) -> (k<>kw || (not (eq_value_t v2 v))) | _ -> true) ol in
  (*Printf.printf "list1 => %s\n" (str_x_list str_opt_t ol ", ");
  Printf.printf "list2 => %s\n" (str_x_list str_opt_t ol2 ", ");*)
  let is_inl = (List.length ol2) <> (List.length ol) in
  (is_inl, ol2)

let opt_list_lookup (ol : opt_t list) (kw : symb) : (value_t option * opt_t list) =
  let (ol_yes,ol_no) = List.partition (fun x -> match x with ValOption(_,Some(k),v2) -> k=kw | _ -> false) ol in
  (*Printf.printf "list1 => %s\n" (str_x_list str_opt_t ol ", ");
  Printf.printf "list2 => %s\n" (str_x_list str_opt_t ol2 ", ");*)
  let result = (try (match List.hd ol_yes with ValOption(_,_,v) -> Some(v) | _ -> None) with _ -> None) in
  (result, ol_no)

let modify_code (p : pos_t) (cd : code option) f (default : string) : code option =
(*match cd with Some(Code(p,c)) -> Some(Code(p,f c)) | _ -> cd*)
Some(Code(p,f (match cd with Some(Code(p,c)) -> c | _ -> default)))

(* HANDLE PROPERTIES *)

let lookup_code (cl : (symb option * code) list) (kw : symb option) : code option =
  (try Some(snd (List.find (fun (s,c) -> s=kw) cl)) with Not_found -> None)

let rec handle_props_tokens (g : grammar_t) : (grammar_t*int) = match g with
| Grammar(pos,(d,dl)) ->
  let (dl2,count) = List.fold_left (fun (acc,index) d -> (match d with
    | PropDecl(p,name,value) -> (
      match (get_symbol name,value) with
      | ("default_production_type",StringVal(p,s)) -> Flags.def_prod_type := str_to_rule_type p s
      | ("default_production_name",StringVal(p,s)) -> Flags.def_prod_name := s
      | ("parameter_name",StringVal(p,s)) -> Flags.param_name := s
      | ("type_name",StringVal(p,s)) -> Flags.type_name := s
      | ("lexer_code",CodeVal(p,(s,c))) -> Flags.lexer_code := Some(s,c,p)
      | ("parser_code",CodeVal(p,(s,c))) -> Flags.parser_code := Some(s,c,p)
      | ("ast_code",CodeVal(p,(s,c))) -> Flags.ast_code := Some(s,c,p)
      | ("utils_code",CodeVal(p,(s,c))) -> Flags.utils_code := Some(s,c,p)
      | ("libs",StringVal(p,s)) -> Hashtbl.clear Flags.libs; List.iter (fun lib -> Hashtbl.replace Flags.libs lib ()) (Str.split (Str.regexp "[ \t\r\n]*,[ \t\r\n]*") s)
      | _ -> die_error p "invalid property name or type"
      );
      acc
    | TokenDecl(p,(name,namel),(ol,(cd,ty1))) -> (
      let ty2 = (match ty1 with
      | None -> Some(SimpleType(p,NoType(p)))
      | Some(SimpleType(p,AnyType(_))) -> Some(SimpleType(p,NoType(p)))
      | _ -> ty1
      ) in
      (TokenDecl(p,(name,namel),(ol,(cd,ty2))))::acc
    )
    | _ -> (d::acc)), index+1
  ) ([],0) (d::dl) in
  let dl2 = List.rev dl2 in
  (Grammar(pos,(List.hd dl2,List.tl dl2)),count)

(* COLLECT NAMED CODE *)

type code_hashtbl = (symb,pos_t*(symb option*code) list) Hashtbl.t

let collect_named_code (g : grammar_t) (count : int) : (grammar_t * code_hashtbl) = match g with
| Grammar(pos,(d,dl)) ->
  let code_table = (Hashtbl.create count : code_hashtbl) in
  let dl2 = List.fold_left (fun (acc) d -> (match d with
    | CodeDecl(p,name,(c,cl)) ->
      let l = (c::cl) in
      Hashtbl.replace code_table name (p,l);
      acc
    | _ -> (d::acc))
  ) ([]) (d::dl) in
  let dl2 = List.rev dl2 in
  (Grammar(pos,(List.hd dl2,List.tl dl2)),code_table)

(* INLINE NAMED CODE *)

let inline_opt (code_table : code_hashtbl) (o : opt_t) : opt_t list = 
(match o with 
  | CodeNameOption(p,s) ->
    let (p2,codes) = (try Hashtbl.find code_table s with Not_found -> die_error p ("could not find code declaration named '"^(get_symbol s)^"'")) in
    let o2 = List.rev (List.rev_map (fun (x,y) -> CodeOption(p2,x,y)) codes) in
    o2
  | _ -> [o])

let inline_opt_list (ol : opt_t list) (code_table : code_hashtbl) : opt_t list = 
rev_flatten (List.rev_map (inline_opt code_table) ol)

let rec inline_grammar (g : grammar_t) (code_table : code_hashtbl) : grammar_t = match g with
| Grammar(pos,(d,dl)) -> Grammar(pos,(inline_decl code_table d, List.rev (List.rev_map (inline_decl code_table) dl)))

and inline_decl (code_table : code_hashtbl) (d : decl_t) : decl_t = match d with
| ProdDecl(p,prod) -> ProdDecl(p,inline_production code_table prod)
| _ -> d

and inline_production (code_table : code_hashtbl) (p : production_t) : production_t = match p with
| Production(ps,(x1,(x2,(opts,ty))),patl) -> Production(ps,(x1,(x2,(inline_opt_list opts code_table,ty))),List.rev (List.rev_map (inline_pattern code_table) patl))

and inline_pattern (code_table : code_hashtbl) (p : pattern_t) : pattern_t = match p with
| Pattern(p,(al,xo)) -> Pattern(p,(List.rev (List.rev_map (inline_annot_atom code_table) al),(match xo with Some(x2,(opts,ty)) -> Some(x2,(inline_opt_list opts code_table,ty)) | None -> None)))

and inline_annot_atom (code_table : code_hashtbl) (an : annot_atom_t) : annot_atom_t = match an with
| SingletonAnnotAtom(p,a) -> SingletonAnnotAtom(p,inline_atom code_table a)
| QuantAnnotAtom(p,an,q) -> QuantAnnotAtom(p,inline_annot_atom code_table an,q)
| OptAnnotAtom(p,an,(opts,(c,ty))) -> OptAnnotAtom(p,inline_annot_atom code_table an,(inline_opt_list opts code_table,(c,ty)))

and inline_atom (code_table : code_hashtbl) (a : atom_t) : atom_t = match a with
| ProdAtom(p,prod) -> ProdAtom(p,inline_production code_table prod)
| _ -> a

(* FLATTEN PRODUCTIONS *)

let flatten_list g f l defname deftyp nesting code_table len f2 =
let (l2,prods,_) = List.fold_left (fun (l2,prods,index) x ->
  let (x2,prods2) = g (f x defname deftyp (index::nesting) code_table ((f2 x) && len=1)) in
  ((x2::l2), List.rev_append prods2 prods, index+1)
) ([],[], !Flags.def_prod_index) l in
(List.rev l2, List.rev prods)

let flatten_opt_list (p : pos_t) ((ol,(co,tyo)) : (opt_t list*(code option * typ_t option))) (deftyp : rule_type option) (nesting : int list)
(code_table : code_hashtbl) : (opt_t list*(code option * typ_t option)) =
  let nesting_len = List.length nesting in
  let ol_len = (List.length ol)+(match tyo with None -> 0 | _ -> 1) in
  if ol_len > 0 && nesting_len > 1 && is_processing_lexer deftyp then
    die_error p "nested lexer productions cannot have names or annotations";
  (ol,(co,tyo))

let rec flatten_grammar (g : grammar_t) (code_table : code_hashtbl) : grammar_t = match g with
| Grammar(pos,(d,dl)) ->
  (*let dl2 = List.rev_map (fun d -> let (x,y) = flatten_decl d in List.rev (x::y)) (d::dl) in
  let l = rev_flatten dl2 in*)
  let the_list = (d::dl) in
  let b = ((List.length the_list)=1) in
  let (dl2,_) = List.fold_left (fun (acc,index) d -> let (x,y) = flatten_decl d None None [index] code_table b in (List.rev_append (x::y) acc, index+1)) ([],!Flags.def_prod_index) the_list in
  let l = List.rev dl2 in
  Grammar(pos,(List.hd l,List.tl l))

and flatten_decl (d : decl_t) (defname : symb option) (deftyp : rule_type option) (nesting : int list) (code_table : code_hashtbl) (is_singleton : bool) : (decl_t*decl_t list) = match d with
| ProdDecl(p,prod) ->
  let (prod2,dl) = flatten_production prod defname deftyp nesting code_table is_singleton in
  (ProdDecl(p,prod2),dl)
| _ -> (d,[])

and flatten_production (p : production_t) (defname : symb option) (deftyp : rule_type option) (nesting : int list) (code_table : code_hashtbl) (is_singleton : bool) : (production_t*decl_t list) = match p with
| Production(ps,o,patl) ->
  let nesting_old = nesting in
  let (defname,deftyp,nesting) = (match o with
    | (kwo,(Some(name),ol)) -> (Some(name),kwo,[])
    | _ -> (defname,deftyp,nesting)
  ) in
  let o2 = (match o with
  | (None,(None,ol)) -> (Some(get_def_prod_type deftyp),(Some(get_def_prod_name defname nesting),([],(None,None))))
  | (None,(Some(name),ol)) -> (Some(get_def_prod_type deftyp),(Some(name),flatten_opt_list ps ol deftyp nesting_old code_table))
  | (Some(kw),(None,ol)) -> (Some(kw),(Some(get_def_prod_name defname nesting),flatten_opt_list ps ol deftyp nesting_old code_table))
  | (Some(kw),(Some(name),ol)) -> (Some(kw),(Some(name),flatten_opt_list ps ol deftyp nesting_old code_table))
  ) in
  let (patl2,prods) = flatten_list (fun x -> x) flatten_pattern patl defname deftyp nesting code_table (List.length patl) (fun x -> true) in
  (Production(ps,o2,patl2),prods)

and flatten_pattern (p : pattern_t) (defname : symb option) (deftyp : rule_type option) (nesting : int list) (code_table : code_hashtbl) (is_singleton : bool) : (pattern_t*decl_t list) = match p with
| Pattern(p,(al,xo)) ->
  (*let len = (match xo with Some(name,(opts,(cd,Some(ty)))) -> 2 | Some(name,(opts,(Some(cd),ty))) -> 2 | _ -> List.length al) in*)
  let len = (match xo with Some(_) -> 2 | _ -> List.length al) in
  let (al2,prods) = flatten_list (fun (x,y,z) -> (x,y)) (flatten_annot_atom []) al defname deftyp nesting code_table len
    (fun x -> match x with QuantAnnotAtom(_,_,_) -> is_singleton | _ -> true) in
  (Pattern(p,(al2,match xo with Some(n,o) -> Some(n,(flatten_opt_list p o deftyp nesting code_table)) | None -> None)),prods)

and flatten_annot_atom (above_opts : opt_t list) (an : annot_atom_t) (defname : symb option) (deftyp : rule_type option) (nesting : int list) (code_table : code_hashtbl) (is_singleton : bool) : (annot_atom_t*decl_t list*bool(*above_opts_consumed*)) = match an with
| SingletonAnnotAtom(p,a) -> flatten_atom above_opts a defname deftyp nesting code_table is_singleton
| QuantAnnotAtom(p,an,q) ->
  let check = (false && is_singleton) || (is_processing_lexer deftyp) in
  let (a2,prods,consumed) = flatten_annot_atom [] an defname deftyp (if check then nesting else (!Flags.def_prod_index::nesting)) code_table false in
  let y = QuantAnnotAtom(p,a2,q) in
  if check then (y,prods,false)
  else
    let name = Flags.get_def_prod_name defname nesting in
    let rt = Flags.get_def_prod_type deftyp in
    (SingletonAnnotAtom(p,IdentAtom(p,name)),
    (ProdDecl(p,Production(p,((Some(rt)),
    (Some(name),([ValOption(p,Some(auto_kw),BoolVal(p,false))]@
    (match rt with Ast -> [ValOption(p,Some(delete_kw),BoolVal(p,true))] | _ -> []),(None,None)))),
      [Pattern(p,([y],Some(None,([],(None,None)))))])))::prods,false)
| OptAnnotAtom(p,an,(o,(((tcd,tty)) as x))) ->
  if is_processing_lexer deftyp then
    die_error p "lexer productions can only contain annotations on the left-hand-side (i.e. applied to the entire production)";
  let is_simple = (match an with SingletonAnnotAtom(_,(ProdAtom(_,_))) -> false | _ -> true) in
  let is_notype = (match tty with None -> true | Some(SimpleType(_,NoType(_))) -> true | _ -> false) in
  (* tty=None && is_singleton *)
  let check = (is_notype && (is_singleton || (is_simple && tcd=None))) in (* check=true iff we don't need more flattening *)
  let (a2,prods,consumed) = flatten_annot_atom o an defname deftyp (if check then nesting else (!Flags.def_prod_index::nesting)) code_table false in
  if check then (OptAnnotAtom(p,a2,((if consumed then [] else o),x)),prods,false)
  else
    let name = Flags.get_def_prod_name defname nesting in
    let rt = Flags.get_def_prod_type deftyp in
    (SingletonAnnotAtom(p,IdentAtom(p,name)),
    (ProdDecl(p,Production(p,((Some(rt)),
    (Some(name),([ValOption(p,Some(auto_kw),BoolVal(p,false))]@
    (match rt with Ast -> [ValOption(p,Some(delete_kw),BoolVal(p,true))] | _ -> []),(None,None)))),
      [Pattern(p,([OptAnnotAtom(p,a2,((if consumed then [] else o),x))],None))])))::prods,false)

and is_inlined p (ol,(co,tyo)) : (bool * (opt_t list * (code option * typ_t option))) =
  let (is_inl, ol2) = opt_list_contains ol inline_kw (BoolVal(NoPos,true)) in
  (is_inl, ((if is_inl then (ol2@[ValOption(p,Some(auto_kw),BoolVal(p,false))]) else ol2),(co,tyo)))

and flatten_atom (above_opts : opt_t list) (a : atom_t) (defname : symb option) (deftyp : rule_type option) (nesting : int list) (code_table : code_hashtbl) (is_singleton : bool) : (annot_atom_t*decl_t list*bool) = match a with
| IdentAtom(p,_) ->
  if is_processing_lexer deftyp then
    die_error p "lexer productions cannot reference other productions";
  (SingletonAnnotAtom(p,a),[],false)
| ProdAtom(p,Production(p2,(kwo,(nameo,((xx,yy) as ol))),patl)) ->
  let name, nesting, defname = (match nameo with
  | Some(name) -> 
    if is_processing_lexer deftyp then die_error p2 "nested lexer productions cannot have names"
    else (name, [], Some(name))
  | None -> (Flags.get_def_prod_name defname nesting, nesting, defname)
  ) in
  let (patl2,prods) = flatten_list (fun x -> x) flatten_pattern patl defname (match kwo with None -> deftyp | _ -> kwo) nesting code_table (List.length patl) (fun x -> true) in
  if is_processing_lexer deftyp then (SingletonAnnotAtom(p,ProdAtom(p,Production(p2,(Some(Lexer),(None,flatten_opt_list p2 ol deftyp nesting code_table)),patl2))),[],false) (* TODO XXX *)
  else (
    let ol = (fst (combine_opt_list (xx@above_opts)), yy) in
    let (is_inl, ol) = is_inlined p ol in
    let result = Production(p2,((match kwo with None -> Some(Flags.get_def_prod_type deftyp) | _ -> kwo),
      (Some(name),(let (x,y) = flatten_opt_list p2 ol deftyp nesting code_table in (x,y)))),patl2) in
    if false(*TODO*) && is_singleton then (SingletonAnnotAtom(p,ProdAtom(p,result)),prods,false)
    else ((if is_inl then
    (*OptAnnotAtom(p,SingletonAnnotAtom(p,IdentAtom(p,name)),([ValOption(p,Some(inline_kw),BoolVal(p,true))],(None,None)))*)
    OptAnnotAtom(p,SingletonAnnotAtom(p,IdentAtom(p,name)),([(*ValOption(p,Some(inline_kw),BoolVal(p,true))*)],
    (None,Some(CompoundType(p,AbstrType(p,IdentName(p,[name]),[SingletonConstrType(p,SimpleType(p,AnyType(p)))]))))))
      else SingletonAnnotAtom(p,IdentAtom(p,name))),(ProdDecl(p2,result))::prods,true)
  )
(*| ProdAtom(p,Production(p2,(kwo,(Some(name),ol)),patl)) -> 
  let (patl2,prods) = flatten_list flatten_pattern patl (Some(name)) (match kwo with None -> deftyp | _ -> kwo) [] code_table in
  if is_processing_lexer deftyp then die_error p2 "nested lexer productions cannot have names"
  else ( 
    let result = Production(p2,((match kwo with None -> Some(Flags.get_def_prod_type deftyp) | _ -> kwo),(Some(name),flatten_opt_list p2 ol deftyp nesting code_table)),patl2) in
    if false(*TODO*) && is_singleton then (ProdAtom(p,result),prods)
    else (IdentAtom(p,name),(ProdDecl(p2,result))::prods)
  ) *)
| EmptyAtom(p)
| EofAtom(p) -> (SingletonAnnotAtom(p,a),[],false)
| CharsetAtom(p,_,_)
| RecurAtom(p,_,_)
| StringAtom(p,_) ->
  if ((not (is_processing_parser deftyp))(* || is_singleton*)) then (SingletonAnnotAtom(p,a),[],false)
  else
  let name = Flags.get_def_prod_name defname nesting in
  (SingletonAnnotAtom(p,IdentAtom(p,name)),[ProdDecl(p,Production(p,(Some(Lexer),(Some(name),(above_opts,(None,None)))),[Pattern(p,([SingletonAnnotAtom(p,a)],None))]))],true)

(*********************************************************)

let mk_compound_type ps t kw =
CompoundType(ps,CommaType(ps,[[InstConstrType(ps,SingletonConstrType(ps,SimpleType(ps,t)),[kw])]]))

let rec elim_grammar (g : grammar_t) : grammar_t = match g with
| Grammar(pos,(d,dl)) -> Grammar(pos,(elim_decl d, List.map elim_decl dl))

and elim_decl (d : decl_t) : decl_t = match d with
| ProdDecl(p,prod) -> ProdDecl(p,elim_production prod)
| _ -> d

and elim_production (p : production_t) : production_t = match p with
| Production(ps,(Some(Lexer),_),_) -> p
| Production(ps,(r,(Some(name),(opts,(cd,ty)))),patl) ->
  (*Printf.printf "before = %s\n" (str_x_list str_opt_t opts "; ");*)
  let (is_auto,opts(* <- TODO XXX okay to not use opts' ?*)) = (opt_list_contains opts auto_kw (BoolVal(NoPos,false))) in
  (*Printf.printf "after = %s\n" (str_x_list str_opt_t opts "; ");*)
  let is_auto = not is_auto in
  let (x,(b,o)) = (List.fold_left (fun (acc,(acc2,acc3)) x -> let (y,(b,o)) = elim_pattern x name is_auto in (List.rev_append y acc, ((b||acc2),
    (match acc3 with None -> o | _ -> acc3)))) ([],(false,None)) patl) in
  Production(ps,(r,(Some(name),(opts,((if b then Some(Code(ps,"List.rev x")) else cd),
    (match o with Some(kw) -> Some(mk_compound_type ps (AnyType(ps)) kw) | _ -> 
    if is_auto || true (* TODO XXX *) then ty else Some(SimpleType(ps,AnyType(ps)))))))),List.rev x)
| Production(ps,_,_) -> die_error ps "production did not acquire a name"

and elim_pattern (pa : pattern_t) (prod_name : symb) (is_auto : bool) : (pattern_t list * (bool*symb option)) = match pa with
(*| Pattern(p,([QuantAnnotAtom(p2,SingletonAnnotAtom(p3,a),q)],xo)) -> [pa] (*TODO*)*)
(*| Pattern(p,([QuantAnnotAtom(p2,OptAnnotAtom(p3,a,yo),q)],xo)) ->*)
| Pattern(p,([QuantAnnotAtom(p2,an,q)],xo)) ->
  (* we expect an OptAnnotAtom below, so make wrap SingletonAnnotAtom appropriately *)
  let an = (match an with SingletonAnnotAtom(p,_) -> OptAnnotAtom(p,an,([],(None,None))) | _ -> an) in
  let (xo,right,an2,xo2) = (match an with
  | OptAnnotAtom(p2,a,(opts,(cd,ty))) ->
    let (left,opts) = opt_list_contains opts recur_kw (StringVal(NoPos,"left")) in
    let (right,opts) = opt_list_contains opts recur_kw (StringVal(NoPos,"right")) in
    ((match q with PlusQuant(p) -> Some(None,([],(modify_code p cd (fun x -> "["^x^"]") "$1",Some(mk_compound_type p (AnyType(p)) list_kw))))
    | QuestionQuant(p) -> Some(None,([],(Some(Code(p,"None")),Some(mk_compound_type p (AnyType(p)) option_kw))))
    | StarQuant(p) -> Some(None,([],(Some(Code(p,"[]")),Some(mk_compound_type p (AnyType(p)) list_kw))))
    ), right, a,
    (match q with
    | QuestionQuant(p) -> Some(None,([],(modify_code p cd (fun x -> "Some("^x^")") "$1",
    Some(mk_compound_type p (VarType(p,add_symbol (!Flags.type_name^"1"))) option_kw))))
    | _ -> let (first,second) = (if right then ("1","2") else ("2","1")) in
    Some(None,([],(modify_code p cd (fun x -> ("let "^ !Flags.param_name^" = $"^first^" in ("^x^")::$"^second)
    ) !Flags.param_name,Some(mk_compound_type p (VarType(p,add_symbol (!Flags.type_name^first))) list_kw))))
    ))
  | _ -> (None,false,an,xo)
  ) in
  let an = (match q with PlusQuant(p) -> an2 | _ -> SingletonAnnotAtom(p,EmptyAtom(p))) in
  ([Pattern(p,([an],xo));
    Pattern(p,((if right then List.rev else (fun x -> x))
    (match q with QuestionQuant(p) -> [an2] | _ -> [SingletonAnnotAtom(p,IdentAtom(p,prod_name));an2]),xo2))],
    (match q with QuestionQuant(_) -> (false,Some(option_kw)) | _ -> ((not right),Some(list_kw))))
| Pattern(p,([OptAnnotAtom(p2,a,(opts,(None,None)))],None)) ->
  ([Pattern(p,((if opts=[] then [a] else [OptAnnotAtom(p2,a,(opts,(None,None)))]),None))], (false,None))
| Pattern(p,([OptAnnotAtom(p2,a,(opts,(cd,ty)))],None)) ->
  let ty = (match ty with Some(SimpleType(_,AnyType(_))) -> Some(SimpleType(p2,VarType(p2,add_symbol (!Flags.type_name^"1")))) | _ -> ty) in
  let ty2 = (match ty with Some(ty) -> (if (not is_auto) then Some(ty)
  else None(*Some(CompoundType(p2,AbstrType(p2,AnyName(p2),[SingletonConstrType(p2,ty)])))*) ) | None -> None) in
  ([Pattern(p,([OptAnnotAtom(p2,a,(opts,(None,None)))],Some(None,([],(cd,ty2)))))], (false,None))
| _ -> ([pa],(false,None))

(*

1 2 3 # 5 6 7 8 # 9 10

9 10 # 5 6 7 8 # 1 2 3

8 7 6 5 10 9


*)
(*********************************************************)
(**  TOPOLOGICAL SORT FUNCTIONALITY                     **)
(*********************************************************)

module IntSet = Set.Make(
struct
  type t = int
  let compare = (Pervasives.compare : (int -> int -> int))
end)

(* (index,lowlink,in_S) *)
type mark = (int * int * bool) option ;;

type simple_graph =
  (int,
    IntSet.t    (* children of this vertex *) *
    mark         (* mark used in topological sort *) *
    bool         (* is_def *) *
    (pos_t * typ_t option) (* definition location, type *)
    (*production_t*) (* TODO XXX *)
  ) Hashtbl.t

(* Tarjan's algorithm - returns a topological sort of the strongly-connected components *)
(* http://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm *)
let rec topo_sort (graph : simple_graph) (vertices : IntSet.t) : (int list) list =
  let stack = ((Stack.create ()) : int Stack.t) in
  let result = fst (Hashtbl.fold (fun k (childs,m,_,_) (res,index) ->
    if (IntSet.mem k vertices) then topo_dfs k res graph index stack else (res,index)
  ) graph ([],0)) in
  (* clear the marks *)
  Hashtbl.iter (fun k (t1,m,t4,t5) ->
    if (m<>None) then Hashtbl.replace graph k (t1,None,t4,t5)
  ) graph;
  result

and topo_dfs (id : int) (res : (int list) list) (graph : simple_graph)
(index : int) (stack : int Stack.t) : ((int list) list * int) =
  let (childs,m,mb,t5) = (try Hashtbl.find graph id with Not_found -> failwith "topo_dfs-1") in
  if (m=None) then (
    (* mark id with (index,index,true) *)
    let v_index = index in
    let v_lowlink = index in
    Hashtbl.replace graph id (childs,Some(v_index,v_lowlink,true),mb,t5);
    let index = index + 1 in
    Stack.push id stack;

    let (res,index,new_v_lowlink) = IntSet.fold (fun child_id (res,index,v_lowlink) ->
      let (_,m,_,_) = (try Hashtbl.find graph child_id with Not_found -> failwith "topo_dfs-2") in
      let (new_v_lowlink,(res,index)) = (match m with
        | None ->
          let (res,index) = topo_dfs child_id res graph index stack in
          let temp = (try Hashtbl.find graph child_id with Not_found -> failwith "topo_dfs-3") in
          let (w_index,w_lowlink,w_in_s) = (match temp with
          | (_,Some(w_index,w_lowlink,w_in_s),_,_) -> (w_index,w_lowlink,w_in_s)
          | _ -> failwith ("topo_dfs-4")) in
          (* update *)
          (min v_lowlink w_lowlink, (res,index))
        | Some((w_index,w_lowlink,w_in_s)) ->
          ((if (w_in_s) then min v_lowlink w_index else v_lowlink), (res,index))
      ) in
      (res,index,new_v_lowlink)
    ) childs (res,index,v_lowlink) in

    Hashtbl.replace graph id (childs,Some(v_index,new_v_lowlink,true),mb,t5);

    if (new_v_lowlink=v_index) then (
      let comp = pop_until graph stack id IntSet.empty in
      ((IntSet.elements comp)::res,index)
    ) else (
      (res,index)
    )
  ) else (
    (res,index)
  )

and pop_until (graph : simple_graph) (stack : int Stack.t) (v : int) (res : IntSet.t) : IntSet.t =
  let w = (try Stack.pop stack with Stack.Empty -> failwith "pop_until-1") in
  let temp = (try Hashtbl.find graph w with Not_found -> failwith "pop_until-1") in
  let (childs,index,lowlink,in_s,mb,t5) = (match temp with
  | (childs,Some(index,lowlink,in_s),mb,t5) -> (childs,index,lowlink,in_s,mb,t5)
  | _ -> failwith ("pop_until-2")) in
  Hashtbl.replace graph w (childs,Some(index,lowlink,false),mb,t5);
  let res2 = (IntSet.add w res) in
  if (w=v) then res2
  else pop_until graph stack v res2

(* BUILD DEFINITION GRAPH *)

let rec build_def_graph_grammar (g : grammar_t) (count : int) : (simple_graph*IntSet.t) = match g with
| Grammar(pos,(d,dl)) ->
  let graph = (Hashtbl.create (10*count)(*TODO XXX - num?*) : simple_graph) in
  (* first go through and find type, position info for all productions *)
  let add p2 name ty1 = (
      let has_type = (match ty1 with None -> false | Some(t) -> is_finalized_typ t) in
      let str = get_symbol name in
      (*Printf.printf ">>>>>> processing name: '%s' = (%b) %s\n%!" str has_type (str_option str_typ_t ty1);*)
      let (x,is_def) = (try (Hashtbl.find graph name, true)
        with Not_found -> ((IntSet.empty,None,false,(p2,if has_type then ty1 else None)),false)) in
      if is_def then die_error p2 ("multiple definition of '"^str^"'")
      else Hashtbl.replace graph name x
  ) in
  let (prod_ids,_) = List.fold_left (fun (prod_ids,indx) d -> (
    (match d with
    | ProdDecl(p,Production(p2,(_,(None,_)),patl)) -> die_error p2 "production is not named"
    | ProdDecl(p,Production(p2,(_,(Some(name),(_,(_,ty1)))),patl)) ->
      add p2 name ty1;
      IntSet.add name prod_ids
    | TokenDecl(p,(name,namel),(ol,(cd,ty1))) ->
      List.iter(fun name -> add p name ty1) (name::namel);
      prod_ids
    | KeywordDecl(p,name,ol,str) ->
      Printf.printf "processing: keyword = %s\n" (get_symbol name);
      add p name (Some(SimpleType(p,NoType(p))));
      prod_ids
    | _ -> prod_ids), indx+1)
  ) (IntSet.empty,0) (d::dl) in
  (* now actually build the graph *)
  List.iter (fun d -> (match d with
    | ProdDecl(p,Production(p2,(_,(None,_)),patl)) -> die_error p2 "production is not named"
    | ProdDecl(p,Production(p2,(_,(Some(name),(_,(_,ty1)))),patl)) ->
      let str = get_symbol name in
      let x = (try let (set,m,is_def,ps) = Hashtbl.find graph name in
        (set,m,true,ps)
        with Not_found -> die_error p ("could not find node '"^str^"' while building graph")) in
      Hashtbl.replace graph name x;
      List.iter (fun pat -> build_def_graph_pattern pat graph name prod_ids) patl
    | _ -> ())
  ) (d::dl);
  (*Hashtbl.iter (fun k (_,_,is_def,(ps,ty)) ->
    if not is_def then die_error ps ("undefined identifier: "^(get_symbol k))
  ) graph;*)
  (graph,prod_ids)

and build_def_graph_pattern (p : pattern_t) (g : simple_graph) (parent : symb) (prod_ids : IntSet.t) : unit =
(*Printf.printf "building pat: %s\n" (str_pattern_t p); *)
match p with
| Pattern(p,(anl,x)) ->
  List.iter (fun an -> build_def_graph_annot_atom an g parent false prod_ids) anl

and build_def_graph_annot_atom (anx : annot_atom_t) (g : simple_graph) (parent : symb) (typed : bool) (prod_ids : IntSet.t) : unit =
(*Printf.printf "building: %s\n" (str_annot_atom_t anx); *)
match anx with
| SingletonAnnotAtom(p,a) -> build_def_graph_atom a g parent typed prod_ids
| QuantAnnotAtom(p,an,q) -> build_def_graph_annot_atom an g parent false prod_ids
| OptAnnotAtom(p,an,(opts,(cd,Some(ty)))) -> build_def_graph_annot_atom an g parent true prod_ids
| OptAnnotAtom(p,an,(opts,(cd,ty))) -> build_def_graph_annot_atom an g parent typed prod_ids

and build_def_graph_atom (a : atom_t) (g : simple_graph) (parent : symb) (typed : bool) (prod_ids : IntSet.t) : unit = match a with
| IdentAtom(p,id) -> 
    let fail id = die_error p ("undefined identifier: "^(get_symbol id)) in
    (* TODO XXX - this "typed" thing doesn't quite work due to the flattening! *)
    let (x1,x2,x3,(x4,tyo)) = (try Hashtbl.find g id with Not_found -> fail id) in
    let has_type = (match tyo with None -> false | Some(t) -> is_finalized_typ t) in
    Hashtbl.replace g id (x1,x2,x3,(x4,tyo));
    (*Printf.printf "%s depends on %s (typed = %b)\n" (get_symbol parent) (get_symbol id) has_type;*)
    let (set,m,is_def,ps) = (try Hashtbl.find g parent with Not_found -> fail parent) in
    Hashtbl.replace g parent ((if has_type || not (IntSet.mem id prod_ids) then set else IntSet.add id set),m,is_def,ps);
| ProdAtom(p,Production(p2,_,pl)) ->
  List.iter (fun x -> build_def_graph_pattern x g parent prod_ids) pl
| _ -> ()

let get_sorted_defs (result : grammar_t) (count : int) : ((symb*pos_t) list * simple_graph) =
  let (graph,prod_ids) = build_def_graph_grammar result count in
  (*Printf.printf "prod_ids = %s\n" (str_x_list get_symbol (IntSet.elements prod_ids) ", ");
  exit 1;*)
  let comps = topo_sort graph prod_ids in
  let x = List.rev_map (fun comp -> match comp with
    | [] -> failwith "topological sort returned empty connected component"
    | a::more ->
      let (_,_,_,(ps,ty1)) = (try Hashtbl.find graph a with Not_found -> (IntSet.empty,None,false,(NoPos,None)) (*TODO XXX fail?*)) in
      if more=[] then (a,ps) else die_error ps ("cyclic defintion: "^(str_x_list get_symbol comp ", "))
  ) comps in
  (x,graph)

(*******************************************)
(** ????????????                          **)
(*******************************************)

let placeholder_char = '*'

let norm_option f o = match o with
| None -> None
| Some(x) -> Some(f x)

let rec norm_production (p : production_t) : production_t = match p with
| Production(_,(rt,(name,(ol,(cd,ty)))),pl) -> Production(NoPos,(rt,(name,(List.rev (List.rev_map norm_opt ol),(norm_option norm_code cd,norm_option norm_typ ty)))),List.rev (List.rev_map norm_pattern pl))

and norm_pattern (p : pattern_t) : pattern_t = match p with
| Pattern(_,(ans,None)) -> Pattern(NoPos,(List.rev (List.rev_map norm_annot_atom ans),None))
| Pattern(_,(ans,Some((name,(ol,(cd,ty)))))) ->
  Pattern(NoPos,(List.rev (List.rev_map norm_annot_atom ans),Some(name,(List.rev (List.rev_map norm_opt ol),(norm_option norm_code cd,norm_option norm_typ ty)))))

and norm_typ (t : typ_t) : typ_t = match t with
| SimpleType(p,st) -> SimpleType(NoPos,norm_simple_type st)
| CompoundType(p,ct) -> CompoundType(NoPos,norm_compound_type ct)

and norm_simple_type (s : simple_type_t) : simple_type_t = match s with
| TokenType(p) -> TokenType(NoPos)
| AnyType(p) -> AnyType(NoPos)
| NoType(p) -> NoType(NoPos)
| VarType(p,s) -> VarType(NoPos,s)
| UnitType(p) -> UnitType(NoPos)
| IdentType(p,sl) -> IdentType(NoPos,sl)

and norm_compound_type (c : compound_type_t) : compound_type_t = match c with
| CommaType(p,cll) -> CommaType(NoPos,List.rev (List.rev_map (fun l -> List.rev (List.rev_map norm_constr_type l)) cll))
| AbstrType(p,an,cl) -> AbstrType(NoPos,norm_abstr_name an,List.rev (List.rev_map norm_constr_type cl))

and norm_abstr_name (a : abstr_name_t) : abstr_name_t = match a with
| IdentName(p,sl) -> IdentName(NoPos,sl)
| AnyName(p) -> AnyName(NoPos)

and norm_constr_type (ct : constr_type_t) : constr_type_t = match ct with
| SingletonConstrType(p,t) -> SingletonConstrType(NoPos,norm_typ t)
| InstConstrType(p,ct,sl) -> InstConstrType(NoPos,norm_constr_type ct,sl)

and norm_opt (o : opt_t) : opt_t = match o with
| ValOption(_,s,v) -> ValOption(NoPos,s,norm_value v)
| CodeOption(_,s,c) -> CodeOption(NoPos,s,norm_code c)
| CodeNameOption(_,s) -> CodeNameOption(NoPos,s)

and norm_value (v : value_t) : value_t = match v with
| BoolVal(_,b) -> BoolVal(NoPos,b)
| IntVal(_,i) -> IntVal(NoPos,i)
| StringVal(_,s) -> StringVal(NoPos,s)
| CharVal(_,c) -> CharVal(NoPos,c)
| CodeVal(_,(s,cd)) -> CodeVal(NoPos,(s,norm_code cd))

and norm_quant (q : quant_t) : quant_t = match q with
| StarQuant(_) -> StarQuant(NoPos)
| PlusQuant(_) -> PlusQuant(NoPos)
| QuestionQuant(_) -> QuestionQuant(NoPos)

and norm_annot_atom (an : annot_atom_t) : annot_atom_t = match an with
| SingletonAnnotAtom(ps,a) -> SingletonAnnotAtom(NoPos,norm_atom a)
| QuantAnnotAtom(ps,an,q) -> QuantAnnotAtom(NoPos,norm_annot_atom an,norm_quant q)
| OptAnnotAtom(ps,an,(opt,(cd,ty))) -> OptAnnotAtom(NoPos,norm_annot_atom an,(List.rev (List.rev_map norm_opt opt),(norm_option norm_code cd,norm_option norm_typ ty)))

and norm_charset (c : charset_t) : charset_t = match c with
| WildcardCharset(_) -> WildcardCharset(NoPos)
| SingletonCharset(_,c) -> SingletonCharset(NoPos,c)
| ListCharset(_,b) -> ListCharset(NoPos,b)

and norm_atom (a : atom_t) : atom_t = match a with
| EmptyAtom(ps) -> EmptyAtom(NoPos)
| EofAtom(ps) -> EofAtom(NoPos)
| StringAtom(ps,str) -> StringAtom(NoPos,str)
| IdentAtom(ps,s) -> IdentAtom(NoPos,s)
| CharsetAtom(ps,c1,c2o) -> CharsetAtom(NoPos,norm_charset c1,norm_option norm_charset c2o)
| RecurAtom(ps,s1,s2) -> RecurAtom(NoPos,s1,s2)
| ProdAtom(ps,pr) -> ProdAtom(NoPos,norm_production pr)

module PatternsHash = Hashtbl.Make(
struct
  type t = pattern_t list
  let hash a = Hashtbl.hash (List.rev_map norm_pattern a)
  let equal a b = ((List.rev_map norm_pattern a)=(List.rev_map norm_pattern b))
end);;

let rec get_placeholder_value_production (p : production_t) : value_t = match p with
| Production(ps,(rto,(nameo,ol)),[]) ->
  die_error ps "unexpected empty production"
| Production(ps,(rto,(nameo,ol)),pl) -> (* NOTE - pl is non-empty here *)
  List.fold_left (fun res pa ->
    let v = get_placeholder_value_pattern pa in
    match (v,res) with
    | (StringVal(ps1,s1),StringVal(ps2,s2)) -> if (String.length s1)>(String.length s2) then v else res
    | (StringVal(ps1,_),CharVal(ps2,_)) -> v
    | (CharVal(ps1,_),StringVal(ps2,_)) -> res
    | (_,_) -> res
  ) (CharVal(ps,placeholder_char)) pl

and get_placeholder_value_pattern (pa : pattern_t) : value_t = match pa with
| Pattern(ps,(an::[],x)) ->
  get_placeholder_value_annot_atom an
| Pattern(ps,(anl,x)) -> StringVal(ps,String.make 2 placeholder_char)

and get_placeholder_value_annot_atom (an : annot_atom_t) : value_t = match an with
| SingletonAnnotAtom(ps,a) -> get_placeholder_value_atom a
| QuantAnnotAtom(ps,an,q) -> StringVal(ps,String.make 2 placeholder_char)
| OptAnnotAtom(ps,an,opt) -> get_placeholder_value_annot_atom an

and get_placeholder_value_atom (a : atom_t) : value_t = match a with
| EmptyAtom(ps) -> StringVal(ps,String.make 2 placeholder_char)
| EofAtom(ps) -> StringVal(ps,String.make 2 placeholder_char)
| StringAtom(ps,str) -> StringVal(ps,String.make (if (String.length str)=1 then 1 else 2) placeholder_char)
| IdentAtom(ps,s) -> die_error ps ("production name '"^(get_symbol s)^"' should not appear in a lexer production")
| CharsetAtom(ps,c1,c2o) -> CharVal(ps,placeholder_char)
| RecurAtom(ps,s1,s2) -> StringVal(ps,String.make 2 placeholder_char)
| ProdAtom(ps,pr) -> get_placeholder_value_production pr

let val_to_atom (v : value_t) : (atom_t * int) = match v with
| StringVal(ps,str) -> (StringAtom(ps,str), String.length str)
| CharVal(ps,c) -> (CharsetAtom(ps,SingletonCharset(ps,c),None), 1)
| _ -> failwith ("could not convert value '"^(str_value_t v)^"' to atom")

let rec strip_lexer_grammar (g : grammar_t) (count : int) : (grammar_t * (symb,production_t) Hashtbl.t * (symb*int*typ_t list*IntSet.t) PatternsHash.t) = match g with
| Grammar(pos,(d,dl)) ->
  let the_list = (d::dl) in
  let table = Hashtbl.create count in
  let table2 = PatternsHash.create count in
  let (dl2,_) = List.fold_left (fun (acc,index) x -> ((strip_lexer_decl x table table2 index)::acc, index+1)) ([],0) the_list in
  let l = List.rev dl2 in
  (Grammar(pos,(List.hd l,List.tl l)), table, table2)

and strip_lexer_decl (d : decl_t) (table : (symb,production_t) Hashtbl.t) (table2 : (symb*int*typ_t list*IntSet.t) PatternsHash.t) (index : int) : decl_t = match d with
| ProdDecl(p,(Production(p2,((Some(Lexer),(so,(ol,(olx,ty1)))) (*as name*)),pl) as prod)) ->
  let sym = (match so with
  | Some(s) -> s
  | None -> die_error p2 "un-named lexer production") in
  let (vl,ol2) = opt_list_lookup ol prec_kw in
  Hashtbl.replace table sym prod;
  let prec1 = (match vl with Some(IntVal(_,i)) -> i | _ -> !Flags.def_precedence) in
  let (nm,pr,tys,temp) = (try PatternsHash.find table2 pl with Not_found -> ((*add_symbol (!Flags.lexer_prefix^(string_of_int index))*)sym, prec1, [], IntSet.empty)) in
  let (nm2,prec) = (if prec1 <= pr then (sym,prec1) else (nm,pr)) in
  PatternsHash.replace table2 pl (nm2,prec,(match ty1 with Some(t) -> (norm_typ t)::tys | _ -> (SimpleType(NoPos,AnyType(NoPos)))::tys),(IntSet.add sym temp));
  let (v,len) = val_to_atom (get_placeholder_value_production prod) in
  ProdDecl(p,Production(p2,((Some(Lexer),(so,(ValOption(p,Some(len_kw),IntVal(p2,len))::ol,(olx,ty1))))),[Pattern(p2,([SingletonAnnotAtom(p2,v)],None))]))
| ProdDecl(p,(Production(p2,((Some(Parser),(so,(ol,(olx,ty1))))),pl))) ->
  d
| _ -> d

let restore_lexer_grammar (g : grammar_t) (table : (symb,production_t) Hashtbl.t) : (grammar_t) = match g with
| Grammar(pos,(d,dl)) ->
  let d2 = List.rev (List.rev_map (fun x -> match x with
  | ProdDecl(p,Production(p2,(Some(Lexer),(Some(name),(ol,(cd,ty)))),pl)) ->
    let prod = (try Hashtbl.find table name with Not_found -> die_error p ("could not find lexer body: "^(get_symbol name))) in
    (match prod with
    | Production(p3,(rt2,(name2,(ol2,(cd2,ty2)))),pl2) -> ProdDecl(p,Production(p2,(Some(Lexer),(Some(name),(ol,(cd,ty)))),pl2))
    )
  | _ -> x) (d::dl)) in
  Grammar(pos,(List.hd d2, List.tl d2))

(*******************************************)
(** TYPECHECKING                          **)
(*******************************************)

type prod_hashtbl = (symb,production_t * int) Hashtbl.t

(* TODO XXX - deal with the upper/lowercase issues of ocamlyacc idents *)

let str_code_plain (c : code) =
match c with
| EmptyCode(_) -> ""
| Code(_,s) -> s

exception IncompatibleLists of pos_t

(* returns (is_auto_type, is_any_type) *)
let rec is_auto_type (t : typ_t) (auto_name : symb) : (bool*bool) =
match t with
| CompoundType(_,AbstrType(_)) -> (true,false)
| CompoundType(_,CommaType(_,[[SingletonConstrType(_,t)]])) -> is_auto_type t auto_name
| SimpleType(_,AnyType(_)) -> (true,true)
| SimpleType(_,IdentType(_,[kw])) ->
  (*((kw=(get_auto_type_name prod_name)), false)*)
  ((kw=(auto_name)), false)
| _ -> (false,false)

let rec typecast (cd : code option) (old_types : typ_t list) (new_type : typ_t) (single_param : bool) (rt : rule_type option) (auto_name : symb): code option =
match (rt,cd,new_type) with
| (Some(Ast),_,_) -> cd
| (_,Some(_),_) -> cd
| (_,None,SimpleType(p,_))
| (_,None,CompoundType(p,_)) ->
  let old_t2 = (match old_types with
  | [] -> die_error p "unexpected empty pattern"
  | [t] -> t
  | _ -> (CompoundType(p,CommaType(p,[List.rev (List.rev_map (fun x -> SingletonConstrType(p,x)) old_types)])))
  ) in
  let indices = List.rev (fst (List.fold_left (fun (acc,index) t -> ((match t with SimpleType(_,NoType(_)) -> acc | _ -> (index::acc)), index+1)) ([],1) old_types)) in
  let left_params = (str_x_list (fun x -> "$"^(string_of_int x)) indices ",") in
  (* if this is a conversion between two equivalent types, there's no need for a cast operation *)
  if eq_typ_t old_t2 new_type || (fst (is_auto_type old_t2 auto_name) && fst (is_auto_type new_type auto_name)) then Some(Code(p,if single_param then !Flags.param_name else ("("^left_params^")")))
  else (modify_code p ((typecast_typ !Flags.param_name old_t2 new_type)) (fun x -> (if single_param then "" else ("let "^ !Flags.param_name^" = ("^
  left_params^") in ignore "^ !Flags.param_name^"; "))^"("^x^")") "")

and typecast_constr (arg : string) (old_type : constr_type_t) (new_type : constr_type_t) : code option =
let fail p = die_error p ("don't know how to cast type "^(str_constr_type_t old_type)^" to "^(str_constr_type_t new_type)) in
  match (old_type,new_type) with
  | (SingletonConstrType(p,t1),SingletonConstrType(_,t2)) -> (typecast_typ arg t1 t2)
  | (SingletonConstrType(p,t1),ct2) -> (typecast_typ arg t1 (CompoundType(p,CommaType(p,[[ct2]]))))
  | (ct1,SingletonConstrType(p,t2)) -> (typecast_typ arg (CompoundType(p,CommaType(p,[[ct1]]))) t2)
  | (InstConstrType(p,ct1,[]),InstConstrType(_,ct2,[])) ->
    typecast_constr arg ct1 ct2
  | (InstConstrType(p,ct1,[]),InstConstrType(_,_,l2)) ->
    typecast_constr arg ct1 new_type
  | (InstConstrType(p,_,l1),InstConstrType(_,ct2,[])) ->
    typecast_constr arg old_type ct2
  | (InstConstrType(p1,ct1,l1),InstConstrType(p2,ct2,l2)) ->
    let (kw1,kw2,l1,l2) = (match (List.rev l1, List.rev l2) with
    | (kw1::l1, kw2::l2) -> (kw1,kw2,List.rev l1,List.rev l2)
    | _ -> die_error p1 "unexpected match failure"
    ) in
    if kw1<>kw2 then fail p1
    else (
      let c = typecast_constr arg (InstConstrType(p1,ct1,l1)) (InstConstrType(p2,ct2,l2)) in
      (* TODO XXX - is the following correct? *)
      match c with
      | None -> None
      | Some(c) ->
      Some(
        if kw1=list_kw then Code(p1,"(List.rev (List.rev_map (fun "^arg^" -> "^(str_code_plain c)^") "^arg^"))")
        else if kw1=option_kw then Code(p1,"(match "^arg^" with Some("^arg^") -> Some("^(str_code_plain c)^") | _ -> None)")
        (* TODO XXX - we are handling list,option - do we need any more? *)
        else die_error p1 ("don't have an automatic cast for type "^(get_symbol kw1))
        )
    )

and typecast_lists (arg : string) (p : pos_t) (index : int) (old_types : constr_type_t list) (new_types : constr_type_t list) (inputs : int list) (result : code list) : (int list * code list * int) =
(*Printf.printf "  > casting lists (%d): %s  ==>  %s\n" index (str_x_list str_constr_type_t old_types "; ") (str_x_list str_constr_type_t new_types "; ");*)
let append a l = (match a with None -> l | Some(a) -> a::l) in
  match (old_types,new_types) with
  | ([],[]) -> (*Printf.printf "done lists: %s\n" (str_x_list string_of_int inputs ", ");*) (List.rev inputs,List.rev result,index-1)
  | ((SingletonConstrType(_,SimpleType(_,NoType(_))))::more1,(SingletonConstrType(_,SimpleType(_,NoType(_))))::more2) -> typecast_lists arg p (index+1) more1 more2 inputs result
  | ((SingletonConstrType(_,SimpleType(_,NoType(_))))::more,_) -> typecast_lists arg p (index+1) more new_types inputs result
  (*| (_,(SingletonConstrType(_,SimpleType(_,NoType(_))))::more) -> typecast_lists arg p index old_types more result*)
  | ((SingletonConstrType(_,SimpleType(_,IdentType(_,[kw1]))) as o)::more1,(SingletonConstrType(_,SimpleType(_,IdentType(_,[kw2]))) as n)::more2) when kw1=kw2 ->
      typecast_lists arg p (index+1) more1 more2 (index::inputs) (append (typecast_constr (arg^"_"^(string_of_int index)) o n) result)
  | (_,(SingletonConstrType(_,SimpleType(_,IdentType(_,[kw2]))))::more2) when kw2= !Flags.pos_type_name && !Flags.enable_pos ->
      (* handle the pos_t appropriately *)
      typecast_lists arg p index old_types more2 inputs ((Code(p,"get_current_pos ()"))::result)
  | ((SingletonConstrType(_,SimpleType(_,IdentType(_,[kw2]))))::more,_) when kw2= !Flags.pos_type_name && !Flags.enable_pos ->
      (* handle the pos_t appropriately *)
      typecast_lists arg p (index+1) more new_types inputs result
  | (o::more1,n::more2) -> (
      typecast_lists arg p (index+1) more1 more2 (index::inputs) (append (typecast_constr (arg^"_"^(string_of_int index)) o n) result)
  )
  | ([],SingletonConstrType(p,_)::_)
  | ([],InstConstrType(p,_,_)::_)
  | (SingletonConstrType(p,_)::_,[])
  | (InstConstrType(p,_,_)::_,[]) -> (*Printf.printf "fail lists\n";*) raise (IncompatibleLists(p))

and typecast_typ (arg : string) (old_type : typ_t) (new_type : typ_t) : code option =
(*Printf.printf " > casting %s => %s\n\n" (str_typ_t old_type) (str_typ_t new_type);*)
let fail p b = die_error p ("don't know how to cast type "^(str_typ_t old_type)^" to "^(str_typ_t new_type)^(if b then ": mismatching argument count" else "")) in
(*Printf.printf ">>> trying to convert %s to %s\n" (str_typ_t old_type) (str_typ_t new_type);*)
match (old_type,new_type) with
| (SimpleType(p,IdentType(_,[kw])),SimpleType(_,TokenType(_))) when kw=string_kw ->
  Some(Code(p,"(lookup_token "^arg^")")) (* TODO XXX - this is not correct *)
| (SimpleType(p,IdentType(_,[kw])),SimpleType(_,IdentType(_,[kw2]))) when kw=string_kw && kw2=token_kw ->
  Some(Code(p,"(lookup_token "^arg^")")) (* TODO XXX - this is not correct *)
| (SimpleType(p,TokenType(_)),SimpleType(_,TokenType(_))) ->
  Some(Code(p,arg))
| (_,SimpleType(p,TokenType(_))) ->
  let c = typecast_typ arg old_type (SimpleType(p,IdentType(p,[string_kw]))) in
  (match c with
  | None -> die_error p "failed to first cast to string before casting to token"
  | Some(c) ->
  Some(Code(p,("(lookup_token "^(str_code c)^")"))))
(*| (_,SimpleType(p,IdentType(_,[kw]))) when kw=token_kw ->*)

| (_,SimpleType(p,IdentType(_,[kw]))) when kw=unit_kw ->
  Some(Code(p,"()"))
| (_,CompoundType(p,AbstrType(_,IdentName(_,[name]),[]))) ->
  Some(Code(p,get_symbol name))
| (_,SimpleType(p,NoType(_))) -> (* TODO XXX - ok to just treat NoType as UnitType? (previously returning None here) *)
  None
| (_,CompoundType(p,CommaType(_,[[]])))
| (_,SimpleType(p,UnitType(_))) ->
  Some(Code(p,"()"))
| (CompoundType(p,CommaType(_,[[SingletonConstrType(_,t1)]])),
CompoundType(_,CommaType(_,[[SingletonConstrType(_,t2)]]))) ->
  typecast_typ arg t1 t2
(*| (_,CompoundType(_,CommaType(_,[[SingletonConstrType(_,t2)]]))) ->
  typecast_typ arg old_type t2
| (CompoundType(p,CommaType(_,[[SingletonConstrType(_,t1)]])),_) ->
  typecast_typ arg t1 new_type*)
| (SimpleType(p,NoType(_)),SimpleType(_,IdentType(_,[kw2])))
| (SimpleType(p,UnitType(_)),SimpleType(_,IdentType(_,[kw2])))
| (CompoundType(p,CommaType(_,[[]])),SimpleType(_,IdentType(_,[kw2]))) ->
  (try Some(Code(p,(Hashtbl.find Flags.def_val_table kw2))) with Not_found -> fail p false)
| (SimpleType(p,IdentType(_,[kw1])),SimpleType(_,IdentType(_,[kw2]))) when kw1=unit_kw ->
  (try Some(Code(p,(Hashtbl.find Flags.def_val_table kw2))) with Not_found -> fail p false)
| (SimpleType(p,NoType(_)),_) ->
  typecast_typ arg (CompoundType(p,CommaType(p,[[]]))) new_type
| (SimpleType(p,IdentType(_,[kw1])),SimpleType(_,IdentType(_,[kw2]))) ->
  if kw1=kw2 then Some(Code(p,arg))(*Some(Code(p,if inner then "$1" else !Flags.param_name))*)
  else (try Some(Code(p,(Hashtbl.find Flags.typecast_table (kw1,kw2))^" "^arg)) with Not_found -> fail p false)
(* char list => string *)
| (CompoundType(_,CommaType(_,[[InstConstrType(_,SingletonConstrType(_,SimpleType(_,IdentType(_,[kw1]))),[kw2])]])),SimpleType(p,IdentType(_,[kw])))
    when kw=string_kw && kw1=char_kw && kw2=list_kw ->
    Some(Code(p,"(str_implode "^arg^")"))
(* string => char list *)
| (SimpleType(p,IdentType(_,[kw])),CompoundType(_,CommaType(_,[[InstConstrType(_,SingletonConstrType(_,SimpleType(_,IdentType(_,[kw1]))),[kw2])]])))
    when kw=string_kw && kw1=char_kw && kw2=list_kw ->
    Some(Code(p,"(str_explode "^arg^")"))
| (SimpleType(p,IdentType(_,[kw])),CompoundType(_,CommaType(_,[a::b::l2]))) ->
  let (indices,x,_) = (try typecast_lists arg p 1 [SingletonConstrType(p,old_type)] (a::b::l2) [] [] with IncompatibleLists(p) -> fail p true) in
  Some(Code(p,Printf.sprintf "(%s(%s))"
    (if (List.length indices)>0 then Printf.sprintf "let (%s) = %s in " (str_x_list (fun x -> arg^"_"^(string_of_int x)) indices ",") arg else "")
    (str_x_list (str_code_plain) x ",")
  ))
| (CompoundType(p,CommaType(_,[a::b::l1])),SimpleType(_,IdentType(_,[kw]))) ->
  let (indices,x,_) = (try typecast_lists arg p 1 (a::b::l1) [SingletonConstrType(p,new_type)] [] [] with IncompatibleLists(p) -> fail p true) in
  Some(Code(p,Printf.sprintf "(%s(%s))"
    (if (List.length indices)>0 then Printf.sprintf "let (%s) = %s in " (str_x_list (fun x -> arg^"_"^(string_of_int x)) indices ",") arg else "")
    (str_x_list (str_code_plain) x ",")
  ))
(* unit  ==>  (Foo of unit) *)
(* t'  ==>  (Foo of 't) *)
| (SimpleType(p,UnitType(_)),CompoundType(_,AbstrType(_,IdentName(_,[name]),l2)))
| (SimpleType(p,IdentType(_,[_])),CompoundType(_,AbstrType(_,IdentName(_,[name]),l2))) ->
  let (indices,x,_) = (try typecast_lists arg p 1 [SingletonConstrType(p,old_type)] l2 [] [] with IncompatibleLists(p) -> fail p true) in
  Some(Code(p,Printf.sprintf "(%s%s(%s))"
    (if (List.length indices)>0 then Printf.sprintf "let (%s) = %s in " (str_x_list (fun x -> arg^"_"^(string_of_int x)) indices ",") arg else "")
    (get_symbol name)
    (str_x_list (str_code_plain) x ",")
  ))
(* ('s * 't * ...)  ==>  ('s * 't * ...) *)
| (CompoundType(p,CommaType(_,[l1])),CompoundType(_,CommaType(_,[l2]))) ->
  let (indices,x,_) = (try typecast_lists arg p 1 l1 l2 [] [] with IncompatibleLists(p) -> fail p true) in
  Some(Code(p,Printf.sprintf "(%s(%s))"
    (if (List.length indices)>0 then Printf.sprintf "let (%s) = %s in " (str_x_list (fun x -> arg^"_"^(string_of_int x)) indices ",") arg else "")
    (str_x_list (str_code_plain) x ",")
  ))
(* ('s * 't * ...)  ==>  (Foo of 's * 't * ...) *)
| (CompoundType(p,CommaType(_,[l1])),CompoundType(_,AbstrType(_,IdentName(_,[name]),l2))) ->
  let (indices,x,_) = (try typecast_lists arg p 1 l1 l2 [] [] with ex ->
  (*Printf.printf "!!!try again 1:\n%s\n" (Printexc.to_string ex);*)(try typecast_lists arg p 1 [SingletonConstrType(p,old_type)] l2 [] [] with IncompatibleLists(p) -> fail p true)) in
  Some(Code(p,Printf.sprintf "(%s%s(%s))"
    (if (List.length indices)>0 then Printf.sprintf "let (%s) = %s in " (str_x_list (fun x -> arg^"_"^(string_of_int x)) indices ",") arg else "")
    (get_symbol name)
    (str_x_list (str_code_plain) x ",")
  ))
(* (Foo of 's * 't * ...)  ==>  ('s * 't * ...) *)
| (CompoundType(p,AbstrType(_,IdentName(_,names),l1)),CompoundType(p2,CommaType(_,[l2]))) ->
  let (indices,x,_) = (try typecast_lists arg p 1 l1 l2 [] [] with _ -> (*Printf.printf "!!!try again 2\n";*)(try typecast_lists arg p 1 l1 [SingletonConstrType(p2,new_type)] [] [] with IncompatibleLists(p) -> fail p true)) in
  (*let args = (str_x_list (fun x -> arg^"_"^(string_of_int x)) indices ",") in*)
  let args = (str_x_list (fun x -> arg^"_"^(string_of_int x)) (range 1 (List.length l1)) ",") in
  let c = (str_x_list (str_code_plain) x ",") in
  let str = Printf.sprintf "(match %s with %s)" arg
    (str_x_list (fun sy -> (get_symbol sy)^"("^args^") -> ("^c^")") names " | ") in
  Some(Code(p,str))
(* (Foo of 't)  ==>  't *)
| (CompoundType(p,AbstrType(_,IdentName(_,names),l1)),SimpleType(p2,IdentType(_,[kw]))) ->
  let (indices,x,_) = (try typecast_lists arg p 1 l1 [SingletonConstrType(p2,new_type)] [] [] with IncompatibleLists(p) -> fail p true) in
  (*let args = (str_x_list (fun x -> arg^"_"^(string_of_int x)) indices ",") in*)
  let args = (str_x_list (fun x -> arg^"_"^(string_of_int x)) (range 1 (List.length l1)) ",") in
  let c = (str_x_list (str_code_plain) x ",") in
  let str = Printf.sprintf "(match %s with %s)" arg
    (str_x_list (fun sy -> (get_symbol sy)^"("^args^") -> ("^c^")") names " | ") in
  Some(Code(p,str))
(*
| (CompoundType(p,AbstrType(_,_,l1)),CompoundType(_,AbstrType(_,_,l2))) ->
  let (indices,x,_) = (try typecast_lists arg p 1 l1 l2 [] [] with IncompatibleLists(p) -> fail p true) in
  Some(Code(p,"zzz")) (* TODO XXX *)
  (*Some(Code(p,Printf.sprintf "%d -> %d" (List.length l1) (List.length l2)))*)
*)
| (CompoundType(p,_),_)
| (SimpleType(p,_),_) -> fail p false

let rec unify_typ (old_type : typ_t) (new_type : typ_t) (auto_name : symb) : typ_t =
let fail p = die_error p (Printf.sprintf "could not unify type %s with %s" (str_typ_t old_type) (str_typ_t new_type)) in
match (old_type,new_type) with
| (SimpleType(p,NoType(_)),_) -> old_type
| (_,SimpleType(p2,NoType(_))) -> new_type
| (SimpleType(p,AnyType(_)),_) -> new_type
| (_,SimpleType(p2,AnyType(_))) -> old_type
| (SimpleType(p,TokenType(_)),SimpleType(p2,TokenType(_))) -> old_type
| (SimpleType(p,VarType(_,s1)),SimpleType(p2,VarType(_,s2))) ->
  if s1=s2 then old_type else fail p
| (SimpleType(p,UnitType(_)),SimpleType(p2,UnitType(_))) -> old_type
| (SimpleType(p,IdentType(_,l1)),SimpleType(p2,IdentType(_,l2))) ->
  if l1=l2 then old_type else fail p
| (CompoundType(p,CommaType(p2,ctl1)),CompoundType(_,CommaType(_,ctl2))) ->
  (try CompoundType(p,CommaType(p2,List.rev (List.rev_map2 (fun cl1 cl2 ->
    (try List.rev (List.rev_map2 (fun c1 c2 -> unify_constr_type c1 c2 auto_name) cl1 cl2) with _ -> fail p)
  ) ctl1 ctl2)))
  with _ -> fail p)
| (SimpleType(_,IdentType(_,[kw])),CompoundType(p,AbstrType(p2,an1,cl1))) when kw=auto_name ->
  SimpleType(p,IdentType(p,[auto_name]))
| (CompoundType(p,AbstrType(p2,an1,cl1)),SimpleType(_,IdentType(_,[kw]))) when kw=auto_name ->
  SimpleType(p,IdentType(p,[auto_name]))
| (CompoundType(p,AbstrType(p2,an1,cl1)),CompoundType(_,AbstrType(_,an2,cl2))) ->
  (try CompoundType(p,AbstrType(p2,unify_abstr_name an1 an2,List.rev (List.rev_map2 (fun c1 c2 -> unify_constr_type c1 c2 auto_name) cl1 cl2)))
  with _ -> 
  SimpleType(p,IdentType(p,[auto_name]))
  )
| (SimpleType(p,TokenType(_)),SimpleType(_,_))
| (SimpleType(p,VarType(_,_)),SimpleType(_,_))
| (SimpleType(p,UnitType(_)),SimpleType(_,_))
| (SimpleType(p,IdentType(_,_)),SimpleType(_,_))
| (CompoundType(p,CommaType(_,_)),CompoundType(_,_))
| (CompoundType(p,AbstrType(_,_,_)),CompoundType(_,_))
| (CompoundType(p,_),SimpleType(_,_))
| (SimpleType(p,_),CompoundType(_,_)) -> fail p

and unify_constr_type (t1 : constr_type_t) (t2 : constr_type_t) (auto_name : symb) : constr_type_t =
let fail p = die_error p (Printf.sprintf "could not unify type %s with %s" (str_constr_type_t t1) (str_constr_type_t t2)) in
match (t1,t2) with
| (SingletonConstrType(p,t1),SingletonConstrType(p2,t2)) -> SingletonConstrType(p,unify_typ t1 t2 auto_name)
| (InstConstrType(p,ct1,[]),_) ->
  unify_constr_type ct1 t2 auto_name
| (_,InstConstrType(p2,ct2,[])) ->
  unify_constr_type t1 ct2 auto_name
| (InstConstrType(p,ct1,s1),InstConstrType(p2,ct2,s2)) ->
  if s1=s2 then InstConstrType(p,unify_constr_type ct1 ct2 auto_name,s1) else fail p
| (SingletonConstrType(p,_),InstConstrType(_,_,_))
| (InstConstrType(p,_,_),SingletonConstrType(_,_)) -> fail p

(* TODO XXX *)
and unify_abstr_name (an1 : abstr_name_t) (an2 : abstr_name_t) : abstr_name_t =
(*let fail p = die_error p (Printf.sprintf "could not unify constructor name %s with %s" (str_abstr_name_t an1) (str_abstr_name_t an2)) in*)
match (an1,an2) with
| (AnyName(p),_) -> an2
| (_,AnyName(p)) -> an1
| (IdentName(p,s1),IdentName(p2,s2)) ->
  (*if s1=s2 then an1 else fail p*)
  let u = List.fold_left (fun acc x -> IntSet.add x acc) IntSet.empty s1 in
  let u2 = List.fold_left (fun acc x -> IntSet.add x acc) u s2 in
  IdentName(p,IntSet.elements u2)

let rec infer_type_annot_atom (a : annot_atom_t) (g : simple_graph) (auto_name : symb) : (typ_t*annot_atom_t) =
match a with
| SingletonAnnotAtom(p,EmptyAtom(p2)) ->
  let t = SimpleType(p2,NoType(p2)) in (t,OptAnnotAtom(p,a,([],(None,Some(t)))))
| SingletonAnnotAtom(p,EofAtom(p2)) ->
  let t = SimpleType(p2,NoType(p2)) in (t,OptAnnotAtom(p,a,([],(None,Some(t)))))
| SingletonAnnotAtom(p,StringAtom(p2,s)) ->
  let t = SimpleType(p2,IdentType(p2,[string_kw])) in (t,OptAnnotAtom(p,a,([],(None,Some(t)))))
| SingletonAnnotAtom(p,IdentAtom(p2,name)) ->
  let typo = (try let (_,_,_,(_,x)) = Hashtbl.find g name in x with Not_found ->
    die_error p2 ("wasn't able to typecheck production: "^(get_symbol name))
  ) in
  let t = (match typo with None -> SimpleType(p2,IdentType(p2,[auto_name]))(* <- TODO XXX is this right?? *) | Some(t) -> t) in
  (t,OptAnnotAtom(p,a,([],(None,Some(t)))))
| SingletonAnnotAtom(p,CharsetAtom(p2,cs,cso)) ->
  let t = SimpleType(p2,IdentType(p2,[char_kw])) in
  (t,OptAnnotAtom(p,a,([],(None,Some(t)))))
| SingletonAnnotAtom(p,RecurAtom(p2,s1,s2)) ->
  let t = SimpleType(p2,IdentType(p2,[string_kw])) in
  (t,OptAnnotAtom(p,a,([],(None,Some(t)))))
| OptAnnotAtom(p,a,([],(None,None))) ->
  infer_type_annot_atom a g auto_name
| OptAnnotAtom(p,a,(ol,(None,None))) ->
  let (t,a2) = infer_type_annot_atom a g auto_name in
  (t,OptAnnotAtom(p,a2,(ol,(None,None))))
| OptAnnotAtom(p,a,(ol,(None,(Some(SimpleType(_,NoType(_)) as ty))))) ->
  (ty,OptAnnotAtom(p,a,(ol,(None,Some(ty)))))
| SingletonAnnotAtom(p,ProdAtom(_,_))
| OptAnnotAtom(p,_,_)
| QuantAnnotAtom(p,_,_) -> die_error p "atom was not flattened properly"
(*| SingletonAnnotAtom(p,ProdAtom(p2,pr)) ->
  let (ty,pr2) = infer_type_production pr prod_table in
  (ty,SingletonAnnotAtom(p,ProdAtom(p2,pr2)))
| QuantAnnotAtom(p,a,StarQuant(p2)) ->
  let (old_type,a2) = infer_type_annot_atom a prod_table in
  (CompoundType(p,CommaType(p,[[InstConstrType(p,SingletonConstrType(p,old_type),[list_kw])]])),QuantAnnotAtom(p,a2,StarQuant(p2)))
| QuantAnnotAtom(p,a,PlusQuant(p2)) ->
  let (old_type,a2) = infer_type_annot_atom a prod_table in
  let x = SingletonConstrType(p,old_type) in
  (CompoundType(p,CommaType(p,[[x;InstConstrType(p,x,[list_kw])]])),QuantAnnotAtom(p,a2,PlusQuant(p2)))
| QuantAnnotAtom(p,a,QuestionQuant(p2)) ->
  let (old_type,a2) = infer_type_annot_atom a prod_table in
  (CompoundType(p,CommaType(p,[[InstConstrType(p,SingletonConstrType(p,old_type),[option_kw])]])),QuantAnnotAtom(p,a2,QuestionQuant(p2)))
| OptAnnotAtom(p,a,(ol,(cd,ty))) ->
  let (old_type,a2) = infer_type_annot_atom a prod_table in
  let (needs_cast, new_ty) = (match ty with Some(ty) -> (not (eq_typ_t old_type ty),ty) | None -> (false,old_type)) in
  (new_ty,OptAnnotAtom(p,a2,(ol,((if needs_cast then cd else cd),Some(new_ty))))) (* TODO XXX - do the cast here? *)
  *)

and infer_type_production (pr : production_t) (g : simple_graph) : (typ_t*production_t) =
match pr with
| Production(ps,(rt,(name,(ol,(cd,Some(ty))))),patl) -> (ty,pr) (* TODO XXX *)
| Production(ps,(rt,(name,(ol,(cd,ty)))),patl) -> (SimpleType(ps,AnyType(ps)),pr)

let val_to_atom (v : value_t) : (annot_atom_t*typ_t) =
match v with
| StringVal(p,s) -> (SingletonAnnotAtom(p,StringAtom(p,s)),SimpleType(p,IdentType(p,[string_kw])))
| CharVal(p,c) -> (SingletonAnnotAtom(p,CharsetAtom(p,SingletonCharset(p,c),None)),SimpleType(p,IdentType(p,[char_kw])))
| BoolVal(p,_) | IntVal(p,_) | CodeVal(p,_) -> die_error p "cannot convert value to atom"

let rec replace_vars_typ_opt (tl : typ_t list) (t : typ_t option) : typ_t option =
match t with
| None -> None
| Some(t) -> Some(replace_vars_typ tl t)

and replace_vars_typ (tl : typ_t list) (t : typ_t) : typ_t =
match t with
| (SimpleType(p,VarType(p2,name))) -> 
  let str = get_symbol name in
  let len = String.length (!Flags.type_name) in
  let sn = String.sub str len ((String.length str)-len) in
  (try List.nth tl ((int_of_string sn)-1) with _ -> die_error p ("invalid type variable: "^str))
| (CompoundType(p,CommaType(p2,cll))) -> CompoundType(p,CommaType(p2,List.rev (List.rev_map (fun cl -> List.rev (List.rev_map (replace_vars_constr_type tl) cl)) cll)))
| (CompoundType(p,AbstrType(p2,an,cl))) -> CompoundType(p,AbstrType(p2,an,List.rev (List.rev_map (replace_vars_constr_type tl) cl)))
| _ -> t

and replace_vars_constr_type (tl : typ_t list) (ct : constr_type_t) : constr_type_t =
match ct with
| SingletonConstrType(p,t) -> SingletonConstrType(p,replace_vars_typ tl t)
| InstConstrType(p,ct,sl) -> InstConstrType(p,replace_vars_constr_type tl ct,sl)

let get_underscore_name (prod_name : string) : string =
  let str = prod_name in
  let str = Str.global_replace (Str.regexp "\\([A-Z]\\)") "_\\1" (String.uncapitalize str) in
  let str = (String.lowercase str) in
  str

let get_auto_type_name (prod_name : symb) : symb =
  let str = get_symbol prod_name in
  (*let c = String.get str 0 in
  let str = (if (Char.lowercase c)<>c then ("x"^str) else str)^(!Flags.auto_type_suffix) in*)
  let str = (get_underscore_name str)^(!Flags.auto_type_suffix) in
  add_symbol str

let get_token_name (prod_name : string) : string =
  let s2 = get_underscore_name prod_name in
  (String.uppercase (s2))

let get_parser_name (prod_name : string) : string =
  let s2 = get_underscore_name prod_name in
  (String.lowercase (s2))

let rec is_no_type (t : typ_t) : bool =
match t with
| SimpleType(_,NoType(_)) -> true
| CompoundType(_,CommaType(_,[[SingletonConstrType(_,t)]])) -> is_no_type t
| _ -> false

let typecheck (g : grammar_t) (comps : (symb*pos_t) list) (count : int) (gr : simple_graph) : grammar_t = match g with
| Grammar(pos,(d,dl)) ->
  (* set up a map containing all productions *)
  let prod_table = (Hashtbl.create count : prod_hashtbl) in
  let _ = List.fold_left (fun indx d ->
    (match d with
    (* NOTE - all productions should be named at this point *)
    | ProdDecl(p,(Production(p2,(rto,(Some(name),(ol,(_,tyo)))),pl) as prod)) ->
      Hashtbl.replace prod_table name (prod,indx)
      (*Printf.printf "adding: %s\n%!" (get_symbol name)*)
    | _ -> ());
    indx+1
  ) 0 (d::dl) in
  (*Printf.printf "\n\n----------------------\n";*)

  let prods = List.rev (List.fold_left (fun acc (name,ps) ->
    (* for each production... *)
    let ((Production(p,(rt,(name1,(ol1,(cd1,ty1)))),pl) as prod),indx) =
      (try Hashtbl.find prod_table name
      with Not_found -> die_error ps ("1 could not find production '"^(get_symbol name)^"'")) in
    (*Printf.printf "\n\nstarting %s:\n%s\n" (get_symbol name) (str_production_t prod);*)
    let is_lexer = (match rt with (Some(Lexer)) -> true | _ -> false) in
    let auto_name = get_auto_type_name name in
    let pl = (if is_lexer then
      let (a,ty) = val_to_atom (get_placeholder_value_production prod) in
      [Pattern(p,([a],Some(None,([],(None,Some(ty))))))] else pl) in

    (* Step 1 - compute overall types of the patterns *)
    let (pl2_types,_,init_type) = (List.fold_left (fun (acc,index,init_type) (Pattern(p,(al,xo))) ->
      let temp = (List.rev_map (fun a ->
        let (rt,a2) = (infer_type_annot_atom a gr auto_name) in
        (* TODO XXX - do we need the following check? *)
        (*(if is_finalized_typ rt then () else die_error p "");*)
        (rt,a2)
      ) al) in
      let (al2,tys) = List.fold_left (fun (acc1,acc2) (ty,a) -> ((a::acc1),(ty::acc2))) ([],[]) temp in
      let str = get_symbol name in
      let kw_name = add_symbol (str^"_"^(string_of_int index)) in
      let mk_ty nm = (
        (CompoundType(p,AbstrType(p,
        (* TODO XXX - IdentName *)
        IdentName(p,[
          match nm with
          | Some(kw) -> kw
          | _ -> kw_name
        ]),
        (*List.rev (List.rev_map (fun t -> SingletonConstrType(p,t)) tys)*)
        let result = (List.rev (List.fold_left (fun acc t -> if is_no_type t then acc else SingletonConstrType(p,t)::acc) [] tys)) in
        (if !Flags.enable_pos then (SingletonConstrType(p,SimpleType(p,IdentType(p,[!Flags.pos_type_name])))::result) else result)
        )))
      ) in
      let (init_type,xo2,ty2,ty3) = (match xo with
      | Some(nm,(opts,(cd,ty))) ->
        let ty = replace_vars_typ_opt tys ty in
        let ((_,is_auto),i2) = (match ty with None -> ((false,true),init_type) | Some(ty) -> (is_auto_type ty auto_name, Some(ty))) in
        (i2,Some(nm,(opts,(cd,ty))),(ty),if is_auto && cd=None (* <- TODO XXX is this okay? *) then Some(mk_ty nm) else None)
      | _ -> (init_type,xo,None,Some(mk_ty None))) in
      ((Pattern(p,(al2,xo2)),tys,ty2,ty3,index)::acc,index+1,init_type)
    ) ([],0,None) pl) in

    (*Printf.printf ">> init type = %s\n" (str_option str_typ_t init_type);*)

    (*let ord a b = (match (a,b) with
    | (Some(_),Some(_)) -> 0
    | (Some(_),None) -> 1
    | (None,Some(_)) -> 2
    | (None,None) -> 3) in
    let pl2_types = List.sort (fun (_,_,x1,x2,_) (_,_,y1,y2,_) -> compare (ord x1 x2) (ord y1 y2)) pl2_types in*)
    let pl2_types = List.rev pl2_types in

    (* Step 2 - try to unify the types of the patterns *)
    let (pl2,types,ty) = (List.fold_left (fun (acc,acc2,tyo) ((Pattern(p,(al,xo)) (*as pat*)),tys,xty2,xty3,indx) ->
      (*Printf.printf "current = %s\n" (str_option str_typ_t tyo);
      Printf.printf "pattern %d [%s] = {%s} (%s) (%s)\n" indx (str_pattern_t pat) (str_x_list str_typ_t tys "; ") (str_option str_typ_t xty2) (str_option str_typ_t xty3);*)
      let (is_auto,_) = (match tyo with None -> (true,false) | Some(tyo) -> is_auto_type tyo auto_name) in
      let tyo2 = (match ((if is_auto && xty3<>None then xty3 else xty2),tyo) with
        | (Some(ty),Some(ty2)) -> (*Printf.printf "unify %s / %s\n" (str_typ_t ty) (str_typ_t ty2);*) Some(unify_typ ty ty2 auto_name)
        | (_,Some(ty2)) -> Some(ty2)
        | (Some(ty),_) -> Some(ty)
        | (None,None) -> None
      ) in
      ((Pattern(p,(al,xo)))::acc,tys::acc2,tyo2)
    ) ([],[],init_type) pl2_types) in

    (*let ty = (if name=(add_symbol "OptType") then None else ty) in*)
    (*Printf.printf ">> ty bef = %s\n" (str_option str_typ_t ty);*)

    (* if the LHS type isn't finalized, unify with RHS type *)
    let ty = (match (ty,ty1) with
    | (None,_) -> ty1
    | (_,None) -> ty
    | (Some(t),Some(t2)) -> if is_finalized_typ t then ty else Some(unify_typ t t2 auto_name)) in
    (*Printf.printf ">> ty aft = %s\n" (str_option str_typ_t ty);*)
    (*let pl2 = List.rev pl2 in*)

    (* compute concrete type for RHS *)
    let (is_auto,ty) = (match ty with
    | None -> (true,SimpleType(p,IdentType(p,[auto_name])))
    | Some(t) ->
      let (b,b2) = is_auto_type t auto_name in
      (* if we are looking at the any-type, replace with the concrete automatic
       * type name for this production *)
      (b,if b2 then SimpleType(p,IdentType(p,[auto_name])) else t)
    ) in

    (* compute concrete type for LHS, i.e. the overall type of the production *)
    let ty1 = (match (ty1,ty) with
    | (None,_) -> ty
    | (Some(ty1),ty2) -> if is_finalized_typ ty1 then (ty1) else (unify_typ ty1 ty2 auto_name)) in
    (if is_finalized_typ ty1 then () else die_error p ("this production's overall type "^(str_typ_t ty1)^" contains type variables which can't be eliminated"));

    (*Printf.printf ">>>>>>>> prod type init = %s\n" (str_typ_t ty1);*)
    
    (*let ty = (match ty with CompoundType(_,AbstrType(_,_,_)) -> SimpleType(p,IdentType(p,[auto_name])) | _ -> ty) in*)

    (* NOTE - we now replace the old pattern types with the new ones *)
    let (pl2,_) = List.fold_left2 (fun (acc,index) (Pattern(p,(al,xo))) tys ->
      (*Printf.printf "-----\n";*)
      let str = get_symbol name in
      let kw_name = add_symbol (str^"_"^(string_of_int index)) in
      let mk_ty nm = (if is_auto then
        (CompoundType(p,AbstrType(p,
        (* TODO XXX - IdentName *)
        IdentName(p,[
          match nm with
          | Some(kw) -> kw
          | _ -> kw_name
        ]),
        (*List.rev (List.rev_map (fun t -> SingletonConstrType(p,t)) tys)*)
        let result = (List.rev (List.fold_left (fun acc t -> if is_no_type t then acc else SingletonConstrType(p,t)::acc) [] tys)) in
        (if !Flags.enable_pos then (SingletonConstrType(p,SimpleType(p,IdentType(p,[!Flags.pos_type_name])))::result) else result)
        )))
        else ty
      ) in
      let check new_ty = (if is_finalized_typ new_ty then () else die_error p ("this pattern's overall type "^(str_typ_t new_ty)^" contains type variables which can't be eliminated")) in
      let (xo2,new_ty) = (match xo with
      | Some(name,(opts,(cd,Some(CompoundType(x1,AbstrType(x2,nn,x3)) as ct)))) ->
        let name2 = (match name with None -> kw_name | Some(name) -> name) in
        (* TODO XXX - IdentName *)
        let new_ty = (match nn with IdentName(_) -> ct | _ -> CompoundType(x1,AbstrType(x2,IdentName(x2,[name2]),x3))) in
        check new_ty;
        (*Printf.printf ">> 1 casting %s  =>  %s\n" (str_x_list str_typ_t tys "; ") (str_typ_t new_ty);*)
        (Some(Some(name2),(opts,(typecast cd tys new_ty false rt auto_name,Some(new_ty)))),new_ty)
      | Some(name,(opts,(cd,_))) ->
        let new_ty = mk_ty name in
        check new_ty;
        (*Printf.printf ">> 2 casting %s  =>  %s\n" (str_x_list str_typ_t tys "; ") (str_typ_t new_ty);*)
        (Some((match name with None -> Some(kw_name) | _ -> name),(opts,(typecast cd tys new_ty false rt auto_name,Some(new_ty)))),new_ty)
      | None ->
        let new_ty = mk_ty None in
        check new_ty;
        (*Printf.printf ">> 3 casting %s  =>  %s\n\n" (str_x_list str_typ_t tys "; ") (str_typ_t new_ty);*)
        (Some(Some(kw_name),([],(typecast None tys new_ty false rt auto_name,Some(new_ty)))),new_ty)
      ) in
      (((Pattern(p,(al,xo2)))::acc),index-1)
    ) ([],(List.length pl2)-1) pl2 types in

    (*Printf.printf "processing:\n---------\n%s\n--------\nunified = %s / %s\nauto name = %s\nis auto = %b\ncode = %s\n\n%!"
      (str_production_t prod)
      (str_typ_t ty)
      (str_typ_t ty1)
      (get_symbol auto_name)
      is_auto
      (str_option str_code cd1)
      ;*)

    let ty1xx = if fst (is_auto_type ty1 auto_name) then SimpleType(p,IdentType(p,[auto_name])) else ty1 in
    let ol2 = if is_auto then ol1 else ((ValOption(p,Some(auto_kw),BoolVal(p,false)))::ol1) in
    (*Printf.printf ">>>>>>>> prod type final = %s\n" (str_typ_t ty1xx);*)

    (*Printf.printf ">> trying to cast %s  =>  %s\n" (str_typ_t ty) (str_typ_t ty1);*)
    let result = Production(p,(rt,(name1,(ol2,(typecast cd1 [ty] ty1 true rt auto_name,Some(ty1xx))))),pl2) in
    (*Printf.printf "success:\n%s\n" (str_production_t result);*)
    (* add production type to the table *)
    Hashtbl.replace gr name (IntSet.empty,None,false,(p,Some(ty1xx))); (* TODO XXX - do we need to Hashtbl.find first? *)
    Hashtbl.replace prod_table name (result,(*Some(ty1),*)indx);
    if (*rt<>Some(Ast) &&*) fst (opt_list_contains ol1 delete_kw (BoolVal(NoPos,true))) then acc 
    else (ProdDecl(p,result))::acc
  ) [] comps) in

  let prods = List.sort (fun a b ->
    match (a,b) with
    | ((ProdDecl(ps1,Production(_,(_,(Some(name1),_)),_))),(ProdDecl(ps2,Production(_,(_,(Some(name2),_)),_)))) ->
    let (_,i1) = (try Hashtbl.find prod_table name1
      with Not_found -> die_error ps1 ("2 could not find production '"^(get_symbol name1)^"'")) in
    let (_,i2) = (try Hashtbl.find prod_table name2
      with Not_found -> die_error ps2 ("3 could not find production '"^(get_symbol name2)^"'")) in
    compare i1 i2
    | _ -> die_error NoPos "could not return productions to original order"
  ) prods in
  let l = (List.filter (fun x -> match x with ProdDecl(_,_) -> false | _ -> true) (d::dl)) in
  let l = List.rev_append (List.rev l) prods in
  Grammar(pos,(List.hd l, List.tl l))

(******************************************)
(******************************************)

let rec combine_grammar (g : grammar_t) (lexers : (symb*int*typ_t list*IntSet.t) PatternsHash.t) : grammar_t =
match g with Grammar(p,(d,dl)) ->
(* first make sure that the types of duplicated lexers are compatible *)
let table = Hashtbl.create 100 (* TODO XXX - size? *) in
PatternsHash.iter (fun k (nm,prec,ty,v) ->
  (*let auto = get_auto_type_name nm in*)
  let els = (str_x_list get_symbol (IntSet.elements v) ", ") in
  IntSet.iter (fun x -> if x<>nm then Hashtbl.replace table x nm) v;
  (*Printf.printf "\npatterns = %s\n  new = %s (%s)\n  prec = %d\n  vals = %s\n  types = %s\n" (str_x_list str_pattern_t k ", ") (get_symbol nm) (get_symbol auto) prec els (str_x_list str_typ_t ty ", ");*)
  let (check,_) = List.fold_left (fun (check,acc) t -> match acc with None -> (check,Some(t)) | Some(tx) -> ((check && tx=t),Some(t))) (true,None) ty in
  (if not check then die_error NoPos (Printf.sprintf "lexers (%s) match equivalent patterns, so they must have equivalent overall types" els))
  
) lexers;
Grammar(p,(combine_decl table d, List.rev (List.rev_map (combine_decl table) dl)))

and combine_decl (table : (symb,symb) Hashtbl.t) (d : decl_t) : decl_t = match d with
| ProdDecl(p,pr) -> ProdDecl(p,combine_production table pr)
| _ -> d

and combine_production (table : (symb,symb) Hashtbl.t) (pr : production_t) : production_t = match pr with
| Production(p,(rt,(Some(name),(ol,(cd,ty)))),pl) -> 
  let pl2 = List.rev (List.rev_map (combine_pattern table) pl) in
  (try let _ = Hashtbl.find table name in
    Production(p,(rt,(Some(name),((ValOption(p,Some(delete_kw),BoolVal(p,true)))::ol,(cd,ty)))),pl2)
  with Not_found -> Production(p,(rt,(Some(name),(ol,(cd,ty)))),pl2))
| Production(p,(rt,(nm,(ol,(cd,ty)))),pl) -> 
  let pl2 = List.rev (List.rev_map (combine_pattern table) pl) in
  Production(p,(rt,(nm,(ol,(cd,ty)))),pl2)

and combine_pattern (table : (symb,symb) Hashtbl.t) (pa : pattern_t) : pattern_t = match pa with
| Pattern(p,(anl,x)) ->
  Pattern(p,(List.rev (List.rev_map (combine_annot_atom table) anl),x))

and combine_annot_atom (table : (symb,symb) Hashtbl.t) (an : annot_atom_t) : annot_atom_t = match an with
| SingletonAnnotAtom(p,a) -> SingletonAnnotAtom(p,combine_atom table a)
| QuantAnnotAtom(p,an,q) -> QuantAnnotAtom(p,combine_annot_atom table an,q)
| OptAnnotAtom(p,an,x) -> OptAnnotAtom(p,combine_annot_atom table an,x)

and combine_atom (table : (symb,symb) Hashtbl.t) (a : atom_t) : atom_t = match a with
| IdentAtom(p,i) -> (try let i2 = Hashtbl.find table i in IdentAtom(p,i2) with Not_found -> IdentAtom(p,i))
| ProdAtom(p,pr) -> ProdAtom(p,combine_production table pr)
| _ -> a

(******************************************)
(******************************************)

let rec lex_str_pattern (pa : pattern_t) : string = match pa with
| Pattern(_,(al,_)) -> str_x_list lex_str_annot_atom al " "

and lex_str_annot_atom (an : annot_atom_t) : string = match an with
| SingletonAnnotAtom(_,a) -> lex_str_atom a
| QuantAnnotAtom(_,an,StarQuant(_)) -> (lex_str_annot_atom an)^"*"
| QuantAnnotAtom(_,an,PlusQuant(_)) -> (lex_str_annot_atom an)^"+"
| QuantAnnotAtom(_,an,QuestionQuant(_)) -> (lex_str_annot_atom an)^"?"
| OptAnnotAtom(_,an,_) -> lex_str_annot_atom an

and lex_str_atom (a : atom_t) : string = match a with
| EmptyAtom(ps) -> "\"\""
| EofAtom(ps) -> "eof"
| StringAtom(ps,str) -> Printf.sprintf "%S" str
| CharsetAtom(ps,c1,c2o) -> Printf.sprintf "(%s%s)" (lex_str_charset c1) (str_option (fun c2 -> Printf.sprintf " # %s" (lex_str_charset c2)) c2o)
| ProdAtom(ps,Production(_,_,patl)) -> Printf.sprintf "(%s)" (str_x_list lex_str_pattern patl " | ")
| RecurAtom(ps,_,_)
| IdentAtom(ps,_) -> die_error ps "multiple/nested recursive patterns not allowed in lexer"

and lex_str_charset (c : charset_t) : string = match c with
| WildcardCharset(_) -> "_"
| SingletonCharset(_,c) -> Printf.sprintf "%C" c
| ListCharset(_,(neg,chl)) -> Printf.sprintf "[%s%s]" (if neg then "^ " else "") (str_x_list lex_str_chars chl " ")

and lex_str_chars (ch : chars) : string = match ch with
| SingletonChar(c) -> Printf.sprintf "%C" c
| RangeChar(c1,c2) -> Printf.sprintf "%C-%C" c1 c2

let output_line_num = ref 1
let output_char_num = ref 1
let output_filename = ref 0

let output_lines ps o str = (
  let len = String.length str in
  if len > 0 then (
    let lines = Str.split (Str.regexp "[\n]") str in
let newline = (String.get str ((String.length str)-1))='\n' in
let (lines2,_) = List.fold_left (fun (acc,flag) line -> (((line,not flag)::acc),false)) ([],not newline) (List.rev lines) in
List.iter (fun (line,newline) ->
  let len = String.length line in

  Printf.fprintf o "%s%s" line (if newline then "\n" else "");
  (*Printf.printf ">>> outputted at (line=%d, char=%d): %s\n" !output_line_num !output_char_num line;*)

    let current = (!output_filename,!output_line_num) in
    let set = (try Hashtbl.find lines_table current with Not_found -> PosSet.empty) in
    Hashtbl.replace lines_table current (PosSet.add ((!output_char_num, !output_char_num + len),ps) set);

    output_line_num := !output_line_num + (if newline then 1 else 0);
    if newline then output_char_num := 1 else output_char_num := !output_char_num + (String.length line)

) lines2;
  )
)

let output_warning_msg (ps : pos_t) (f : out_channel) (s1 : string) (s4 : string) (s2 : string) (s3 : string) : unit =
   output_lines ps f (s1^
   s4^" THIS IS AN AUTO-GENERATED FILE PRODUCED BY URUZ!\n"^
   s2^" DO NOT EDIT THIS FILE, since any changes will be\n"^
   s2^" lost when the build is reset via \"make clean\".\n"^
   s2^" This file is based on a user-specified EBNF\n"^
   s2^" grammar, which can be edited as desired.\n"^
   s3)

let reset_output filename = (
  output_line_num := 1;
  output_char_num := 1;
  output_filename := (add_symbol filename)
)

let output_lexer_code filename o prefix g (keywords : (symb*string*pos_t) list) = match g with
| Grammar(pos,(d,dl)) ->
  let recur_prefix = "entry_" in
  reset_output filename;
  output_warning_msg pos o "(*\n" " *" " *" " *)";
  output_lines pos o "\n\n";
  output_lines pos o "{\n";
  output_lines pos o ("   open "^(String.capitalize (prefix^"parser"))^";;\n");
  output_lines pos o ("   open "^(String.capitalize (prefix^"ast"))^";;\n");
  output_lines pos o ("   open "^(String.capitalize (prefix^"utils"))^";;\n\n");
  let (rules,keys) = List.fold_left (fun (acc,acc2) d ->
    match d with
    (* NOTE - name and type should be Some(_) at this point *)
    | ProdDecl(_,(Production(ps,(Some(Lexer),(Some(name),(ol,(cd,Some(ty))))),patl) as prod)) ->
      let (is_key,_) = opt_list_contains ol map_kw (BoolVal(NoPos,true)) in
      let (is_newline,_) = opt_list_contains ol newline_kw (BoolVal(NoPos,true)) in
      let (vl,_) = opt_list_lookup ol order_kw in
      let order = (match vl with Some(IntVal(_,i)) -> i | _ -> !Flags.def_precedence) in
      let (vl2,_) = opt_list_lookup ol len_kw in
      let len = (match vl2 with Some(IntVal(_,i)) -> i | _ -> -1(*TODO XXX*)) in
      (((order,get_symbol name,ty,len,is_key,is_newline,prod)::acc),(if is_key then IntSet.add name acc2 else acc2))
    | _ -> (acc,acc2)
  ) ([],IntSet.empty) (d::dl) in


if not (IntSet.is_empty keys) then (
  let key = IntSet.choose keys in (* TODO XXX - for now we just choose one (there should only be one in the program) *)
  output_lines pos o ("  let tokens = ((Hashtbl.create 100) : ((string,token) Hashtbl.t)) ;;\n");
  output_lines pos o ("  let add_token str vl =\n");
  output_lines pos o ("    try let _ = Hashtbl.find tokens str in\n");
  output_lines pos o ("      (parse_error (\"token \"^str^\" already exists\"))\n");
  output_lines pos o ("    with _ -> Hashtbl.replace tokens str vl\n");
  output_lines pos o ("  ;;\n");
  output_lines pos o ("\n");
  output_lines pos o ("  let lookup_keyword str =\n");
  output_lines pos o ("     try (let x = Hashtbl.find tokens str in x)\n");
  output_lines pos o (Printf.sprintf ("     with _ -> %s str\n") (get_token_name (get_symbol key)));
  output_lines pos o ("  ;;\n");
  output_lines pos o ("\n");
  List.iter (fun (name,str,px) ->
  output_lines px o (Printf.sprintf "  add_token \"%s\" %s ;;\n" str (get_token_name (get_symbol name)));
  ) keywords
);

  (match !Flags.lexer_code with Some(s(*TODO XXX*),c,px) -> output_lines px o (str_code_plain c) | _ -> ());
  output_lines pos o "\n}\n\n";
  output_lines pos o ("(* The type \"token\" is defined in "^(String.capitalize (prefix^"parser.mli"))^" *)\n");
  output_lines pos o "rule token = parse\n";

  (* sort by order annotations *)
  let rules = List.sort (fun (p1,_,_,_,_,_,_) (p2,_,_,_,_,_,_) -> compare p1 p2) rules in
  let get_the_code cd name ty len is_key = (match ty with
        | SimpleType(_,NoType(_)) -> (str_option str_code_plain cd)^"; token lexbuf"
        | SimpleType(_,TokenType(_)) -> get_token_name name
        | SimpleType(_,IdentType(_,[kw])) when kw=token_kw -> get_token_name name
        | SimpleType(_,IdentType(_,[kw])) when kw=string_kw && len=1 -> "let "^ !Flags.param_name^" = String.make 1 "^ !Flags.param_name^" in "^(get_token_name name)^"("^(str_option str_code_plain cd)^")"
        | _ -> (get_token_name name)^"("^(str_option str_code_plain cd)^")"
        ) in
  (* output the normal rules *)
  List.iter (fun (_,name,ty,len,is_key,is_newline,(Production(ps,(r,(nameo,(ol,(cd,tyo)))),patl))) ->
    match patl with
    | [Pattern(_,([SingletonAnnotAtom(_,RecurAtom(px,s1,s2))],_))] ->
      output_lines px o (Printf.sprintf "| \"%s\" { %s%s 0 \"\" lexbuf }\n" s1 recur_prefix (String.lowercase name))
    | _ ->
      let the_code = get_the_code cd name ty len is_key in
      output_lines ps o (Printf.sprintf "| (%s) as %s {ignore %s; %s} (* %s : %s (len = %d) (kw = %b) *)\n"
        (str_x_list lex_str_pattern patl " ")
        !Flags.param_name
        !Flags.param_name
        (if is_key then ("(try lookup_keyword "^ !Flags.param_name^" with _ -> "^the_code^")")
        else if is_newline then ("(let _ = count_newlines "^ !Flags.param_name^" lexbuf in "^the_code^")")
        else the_code)
        (name)
        (str_typ_t ty)
        len
        is_key);
  ) rules;
  output_lines pos o (Printf.sprintf "| eof { %s }\n" !Flags.lexer_eof_token_name);
  output_lines pos o "| _ { lex_error \"lexing error\" lexbuf }\n";
  (* output the recursive rules *)
  List.iter (fun (_,name,ty,len,is_key,is_newline,(Production(ps,(r,(nameo,(ol,(cd,tyo)))),patl))) ->
    match patl with
    | [Pattern(_,([SingletonAnnotAtom(_,RecurAtom(px,s1,s2))],_))] ->
      let the_code = get_the_code cd name ty len is_key in
      let rule_name = recur_prefix^(String.lowercase name) in
      output_lines px o (Printf.sprintf "\nand %s n %s = parse\n" rule_name !Flags.param_name);
      output_lines px o (Printf.sprintf "| \"%s\" { %s (n+1) (%s^\"%s\") lexbuf }\n" s1 rule_name !Flags.param_name s1);
      output_lines px o (Printf.sprintf "| \"%s\" { if (n=0) then (%s) else %s (n-1) (%s^\"%s\") lexbuf }\n" s2 the_code rule_name !Flags.param_name s2);
      output_lines px o (Printf.sprintf "| _ as c { if c='\\n' then do_newline lexbuf;\n");
      output_lines px o (Printf.sprintf "              %s n (Printf.sprintf \"%%s%%c\" %s c) lexbuf }\n" rule_name !Flags.param_name);
    | _ -> ()
  ) rules

module TypHash = Hashtbl.Make(
struct
  type t = typ_t
  let hash a = Hashtbl.hash (norm_typ a)
  let equal a b = ((norm_typ a)=(norm_typ b))
end);;

let rec parser_str_production (g : IntSet.t) (pr : production_t) : string = match pr with
| (Production(ps,(Some(Parser),(Some(name),(ol,(cd,Some(ty))))),patl)) ->
  let pname = get_parser_name (get_symbol name) in
  let s1 = Printf.sprintf "%s:\n| %s%s {%s}\n;\n\n" pname pname !Flags.parser_ident_suffix (match cd with None -> "$1" | Some(cd) -> ("let "^ !Flags.param_name^" = $1 in ignore "^ !Flags.param_name^"; ("^(str_code_plain cd)^")")) in
  Printf.sprintf "%s%s%s:\n%s\n;" s1 pname !Flags.parser_ident_suffix
    (str_x_list (fun p -> "| "^(parser_str_pattern pname g p)) patl "\n")
| _ -> "" (* TODO XXX what do we do here? *)

and parser_str_pattern (pname : string) (g : IntSet.t) (pa : pattern_t) : string = match pa with
| Pattern(p,(al,Some(name,(ol,(cd,ty))))) -> (str_x_list (parser_str_annot_atom pname g) al " ")^(match cd with None -> "" | Some(c) -> " "^(str_code c))
| Pattern(p,(al,None)) -> (str_x_list (parser_str_annot_atom pname g) al " ")

and parser_str_annot_atom (pname : string) (g : IntSet.t) (an : annot_atom_t) : string = match an with
| SingletonAnnotAtom(_,a) -> parser_str_atom pname g a
| QuantAnnotAtom(_,an,_) -> parser_str_annot_atom pname g an
| OptAnnotAtom(_,an,_) -> parser_str_annot_atom pname g an

and parser_str_atom (pname : string) (g : IntSet.t) (a : atom_t) : string = match a with
| EmptyAtom(_) -> !Flags.parser_empty_ident_name (* TODO XXX *)
| EofAtom(_) -> !Flags.lexer_eof_token_name
| IdentAtom(_,i) ->
  let str = get_symbol i in
  (if IntSet.mem i g then let x = (get_parser_name str) in Printf.sprintf "%s%s" x (if x=pname then !Flags.parser_ident_suffix else "")
  else get_token_name str)
| ProdAtom(p,_)
| StringAtom(p,_)
| CharsetAtom(p,_,_)
| RecurAtom(p,_,_) -> die_error p "not all non-parser elements were eliminated"


let output_parser_code filename o prefix g (gr : simple_graph) : (string*(symb*string*pos_t) list) = match g with
| Grammar(pos,(d,dl)) ->
  reset_output filename;
  output_warning_msg pos o "/*\n(" "*" " *" " *) */";
  output_lines pos o "\n\n";
  output_lines pos o "%{\n";
  output_lines pos o ("   open "^(String.capitalize (prefix^"ast"))^";;\n");
  output_lines pos o ("   open "^(String.capitalize (prefix^"utils"))^";;\n\n");
  (match !Flags.parser_code with Some(s(*TODO XXX*),c,px) -> output_lines px o (str_code_plain c) | _ -> ());
  output_lines pos o "\n%}\n\n";
  output_lines pos o (Printf.sprintf "%%token %s\n" !Flags.lexer_eof_token_name);
  (* TODO XXX - replace all output_string with output_lines !! *)

  let tok_table = TypHash.create 100 in (* TODO XXX - size? *)
  let prec_table = Hashtbl.create 100 in

  let add ps ty names ol = (
      let set = (try TypHash.find tok_table ty with Not_found -> IntSet.empty) in
      let set2 = List.fold_left (fun acc name -> IntSet.add name acc) set names in
      TypHash.replace tok_table ty set2;

      let (vl,_) = opt_list_lookup ol prec_kw in
      let (prec,b1) = (match vl with Some(IntVal(_,i)) -> (i,true) | _ -> (!Flags.def_precedence,false)) in
      let (vl2,_) = opt_list_lookup ol assoc_kw in
      let (assoc,b2) = (match vl2 with Some(StringVal(_,s)) -> (Some(s),true) | _ -> (None,false)) in
      if b1 || b2 then (
        let (set,assoc2) = (try Hashtbl.find prec_table prec with Not_found -> (IntSet.empty,None)) in
        let set2 = List.fold_left (fun acc name -> IntSet.add name acc) set names in
        let assoc2 = (match (assoc,assoc2) with
        | (None,_) -> assoc2
        | (_,None) -> assoc
        | (Some(a),Some(a2)) -> if a=a2 then assoc2 else die_error ps ("multiple associativities being used at precedence level "^(string_of_int prec))) in
        Hashtbl.replace prec_table prec (set2,assoc2)
      )
  ) in

  (* add all tokens to the table *)
  let (fp,prods2,prod_ids,keywords) = List.fold_left (fun (fp,acc,acc2,keywords) d ->
    match d with
    (* NOTE - name and type should be Some(_) at this point *)
    | ProdDecl(_,(Production(ps,(Some(Parser),(Some(name),(ol,(cd,Some(ty))))),patl) as prod)) ->
      let (fp2,b) = (match fp with None -> (match !Flags.start_prod with Some(pn) -> (if pn=name then (Some(name,ty,prod),true) else (fp,false)) | _ -> (Some(name,ty,prod),true)) | _ -> (fp,false)) in
      (fp2,(if not b then prod::acc else acc),IntSet.add name acc2,keywords)
    | ProdDecl(_,(Production(ps,(Some(Lexer),(Some(name),(ol,(cd,Some(ty))))),patl))) ->
      add ps ty [name] ol;
      (fp,acc,acc2,keywords)
    | TokenDecl(p,(name,namel),(ol,(cd,ty1))) ->
      (match ty1 with Some(ty) -> add p ty (name::namel) ol | _ -> add p (SimpleType(p,NoType(p))) (name::namel) ol);
      (fp,acc,acc2,keywords)
    | KeywordDecl(p,name,(ol,(cd,ty)),str) ->
      add p (SimpleType(p,NoType(p))) [name] ol;
      (fp,acc,acc2,(name,str,p)::keywords)
    | _ -> (fp,acc,acc2,keywords)
  ) (None,[],IntSet.empty,[]) (d::dl) in
  let prods2 = List.rev prods2 in
  let (start_prod_name,start_prod_ty,start_prod) = (match fp with
  | None -> die_error pos "could not determine start production"
  | Some(x) -> x
  ) in
  let tok_types = TypHash.fold (fun k _ acc -> k::acc) tok_table [] in
  let tok_types = List.sort (fun a b -> compare (str_typ_t a) (str_typ_t b)) tok_types in

  List.iter (fun k ->
    let set = (try TypHash.find tok_table k with Not_found -> IntSet.empty) in
    let l = List.rev_map get_symbol (IntSet.elements set) in
    let l = List.sort compare l in
    if l<>[] then output_string o (Printf.sprintf "%%token %s%s\n"
    (match k with SimpleType(_,NoType(_)) -> "" | _ -> "<"^(str_typ_t k)^"> ") (str_x_list get_token_name l " "))
  ) tok_types;

  let tok_precs = Hashtbl.fold (fun k _ acc -> k::acc) prec_table [] in
  let tok_precs = List.rev (List.sort compare tok_precs) in

  output_lines pos o "/*(* starting with lowest precedence:*)*/\n";
  List.iter (fun prec ->
    let (set,assoc) = (try Hashtbl.find prec_table prec with Not_found -> (IntSet.empty,None)) in
    let assoc = (match assoc with None -> !Flags.def_assoc | Some(a) -> a) in
    if not (IntSet.is_empty set) then output_string o (Printf.sprintf "%%%s %s /*(* %d *)*/\n" assoc
    (str_x_list get_token_name (List.rev_map get_symbol (IntSet.elements set)) " ") prec)
  ) tok_precs;
  output_string o "/*(* ^^ highest precedence *)*/\n";
  let pname = get_parser_name (get_symbol start_prod_name) in
  output_string o (Printf.sprintf "%%start %s /*(* the entry point *)*/\n" pname);
  let ty_str = (match start_prod_ty with
  | SimpleType(_,IdentType(_,[i])) ->
    let s = get_symbol i in
    let pref = chop_end_str s (String.length !Flags.auto_type_suffix) in
    (*Printf.printf ">> looking: %s, %s\n" s pref;*)
    if (pref^ !Flags.auto_type_suffix)=s && (Hashtbl.fold (fun k v acc -> acc || ((String.lowercase (get_symbol k))=pref)) gr false) then
    ((String.capitalize (prefix^"ast."))^s) else s
  | t -> str_typ_t t) in
  output_string o (Printf.sprintf "%%type <%s> %s\n" ty_str pname);
  output_string o (Printf.sprintf "%%%%\n");
  (*output_string o (Printf.sprintf "%s:\n" pname);*)
  output_string o (Printf.sprintf "%s\n\n" (parser_str_production prod_ids start_prod));
  List.iter (fun p ->
    output_string o (Printf.sprintf "%s\n\n" (parser_str_production prod_ids p));
  ) prods2;
  (* add the "empty" token (which presumably returns empty string) *)
  output_string o (Printf.sprintf "%s:\n| {}\n;\n\n" !Flags.parser_empty_ident_name);
  output_string o (Printf.sprintf "%%%%\n");
  output_string o (Printf.sprintf "(* footer code *)\n");
  (pname,keywords)

let str_opt_list f l sep = List.fold_left (fun result x ->
  match (result,f x) with
  | (None,a) -> a
  | (a,None) -> a
  | (Some(result),Some(y)) ->
    Some(result^sep^y)
) None l

let rec ast_str_typ (t : typ_t) : string option = match t with
| SimpleType(p,NoType(_)) -> None 
| SimpleType(_,TokenType(_)) -> Some("token")
| SimpleType(_,UnitType(_)) -> Some("unit")
| SimpleType(_,IdentType(_,sl)) -> Some(str_x_list get_symbol sl ".")
| CompoundType(_,CommaType(_,cll)) ->
  let op = (str_opt_list (fun cl -> str_opt_list ast_str_constr_type cl " * ") cll ", ") in (
    match op with
    | None -> Some("()") (* TODO XXX - is this right? *)
    | Some(x) -> Some("("^x^")")
  )
| CompoundType(_,AbstrType(_,nm,cl)) ->
  Some(Printf.sprintf "%s%s" (ast_str_abstr_name nm)
    (match (cl,(str_opt_list ast_str_constr_type cl " * ")) with ([],_) -> "" | (_,None) -> "" | (_,Some(yy)) -> " of "^yy))
| SimpleType(p,AnyType(_))
| SimpleType(p,VarType(_)) -> (* TODO XXX *) die_error p "don't know how to handle non-AST types"

and ast_str_abstr_name (nm : abstr_name_t) : string = match nm with
| IdentName(_,[s]) -> get_symbol s
| IdentName(p,_)
| AnyName(p) -> (* TODO XXX *) die_error p "don't know how to handle non-AST abstr. name"

and ast_str_constr_type (ct : constr_type_t) : string option = match ct with
| SingletonConstrType(_,t) -> ast_str_typ t
| InstConstrType(_,ct,sl) ->
  let op = (ast_str_constr_type ct) in (
    match op with
    | None -> Some("()") (* TODO XXX - is this right? *)
    | Some(x) -> Some(Printf.sprintf "%s %s" x (str_x_list get_symbol sl " "))
  )

let ast_str_pattern (pa : pattern_t) : string option = match pa with
| Pattern(p,(al,Some(name,(ol,(cd,Some(ty)))))) ->
  ast_str_typ ty
| Pattern(p,(al,_)) -> (* TODO XXX *) die_error p "pattern did not receive name/type"

let output_ast_code filename o prefix g = match g with
| Grammar(pos,(d,dl)) ->
  reset_output filename;
  output_warning_msg pos o "(*\n" " *" " *" " *)";
  output_string o "\n\n";
  output_string o ("open "^(String.capitalize (prefix^"utils"))^";;\n");
  (*(match !Flags.parser_code with Some(s(*TODO XXX*),c) -> output_string o (str_code_plain c) | _ -> ());*)
  output_string o "\n(* AST Data Structure *)\n";
  let _ = List.fold_left (fun first d ->
    match d with
    (* NOTE - name and type should be Some(_) at this point *)
    | ProdDecl(_,(Production(ps,(Some(Parser),(Some(name),(ol,(cd,Some(ty))))),patl)))
    | ProdDecl(_,(Production(ps,(Some(Ast),(Some(name),(ol,(cd,Some(ty))))),patl))) ->
      (match ty with
      | SimpleType(_,NoType(_)) -> first
      | _ ->
        let tn = (get_auto_type_name name) in
        let is_auto = not (fst (opt_list_contains ol auto_kw (BoolVal(NoPos,false)))) in
        output_string o (Printf.sprintf "\n%s %s = " (if first then "type" else "\n and") (get_symbol tn));
        if is_auto then (
          List.iter (fun p ->
            match (ast_str_pattern p) with None -> () | Some(str) -> output_string o (Printf.sprintf "\n   | %s" str)
          ) patl;
        ) else (match (ast_str_typ ty) with None -> () | Some(str) -> output_string o (Printf.sprintf "%s" str));
        false
      )
    | _ -> first
  ) true (d::dl) in
  (match !Flags.ast_code with Some(s(*TODO XXX*),c,px) -> output_string o (str_code_plain c) | _ -> ());
  ()

let output_utils_code filename o prefix g = match g with
| Grammar(pos,(d,dl)) ->
  reset_output filename;
  output_warning_msg pos o "(*\n" " *" " *" " *)";
  output_string o "\n\nopen Lexing;;\n";
  output_string o "open Parsing;;\n";
  output_string o "(* open Flags;; *)\n";
  output_string o "\n";
  output_string o "(* data type for file positions *)\n";
  output_string o "let filename = ref \"\"\n";
  let p = (get_symbol !Flags.pos_type_name) in
  output_string o ("type "^p^" = NoPos | Pos of string*int*int;; (* file,line,col *)\n");
  output_string o "\n";
  output_string o "exception Parse_error of string;;\n";
  output_string o "exception Lexing_error of string;;\n";
  output_string o "exception General_error of string;;\n";
  output_string o "\n";
  output_string o "(* do_error p s\n";
  output_string o " *\n";
  output_string o " * Print error message\n";
  output_string o " *\n";
  output_string o " * p - the location of the error\n";
  output_string o " * s - the error message\n";
  output_string o " *\n";
  output_string o " * returns unit\n";
  output_string o " *)\n";
  output_string o ("let do_error (p : "^p^") (s : string) : string =\n");
  output_string o "   (\"Error\"^\n";
  output_string o "   (match p with\n";
  output_string o "   | NoPos -> \"\"\n";
  output_string o "   | Pos(file_name,line_num,col_num) -> (\" in '\"^file_name^\n";
  output_string o "    \"' on line \"^(string_of_int line_num)^\" col \"^(string_of_int\n";
  output_string o "    col_num))\n";
  output_string o "   )^\n";
  output_string o "   (\": \"^s^\"\\n\"))\n";
  output_string o ";;\n";
  output_string o "\n";
  output_string o ("let die_error (p : "^p^") (s : string) =\n");
  output_string o "   raise (General_error(do_error p s))\n";
  output_string o ";;\n";
  output_string o "\n";
  output_string o "(* gets a pos data structure using the current lexing pos *)\n";
  output_string o "let get_current_pos () =\n";
  output_string o "   let p         = symbol_start_pos () in\n";
  output_string o "   let file_name = !filename (*p.Lexing.pos_fname*)  in\n";
  output_string o "   let line_num  = p.Lexing.pos_lnum   in\n";
  output_string o "   let col_num   = (p.Lexing.pos_cnum-p.Lexing.pos_bol+1) in\n";
  output_string o "   Pos(file_name,line_num,col_num)\n";
  output_string o ";;\n";
  output_string o "\n";
  output_string o "(* gets a pos data structure from a lexing position *)\n";
  output_string o "let get_pos (p : Lexing.position) =\n";
  output_string o "   let file_name = !filename (*p.Lexing.pos_fname*) in\n";
  output_string o "   let line_num  = p.Lexing.pos_lnum  in\n";
  output_string o "   let col_num   = (p.Lexing.pos_cnum-p.Lexing.pos_bol+1) in\n";
  output_string o "   Pos(file_name,line_num,col_num)\n";
  output_string o ";;\n";
  output_string o "\n";
  output_string o "(* dies with a general position-based error *)\n";
  output_string o "let pos_error (s : string) (p : position) = \n";
  output_string o "   do_error (get_pos p) s\n";
  output_string o ";;\n";
  output_string o "\n";
  output_string o "(* dies with a parse error s *)\n";
  output_string o "let parse_error (s : string) = \n";
  output_string o "   raise (Parse_error(pos_error s (symbol_end_pos ())))\n";
  output_string o ";;\n";
  output_string o "\n";
  output_string o "(* dies with a lexing error *)\n";
  output_string o "let lex_error (s : string) (lexbuf : Lexing.lexbuf) = \n";
  output_string o "   raise (Lexing_error(pos_error s (Lexing.lexeme_end_p lexbuf)))\n";
  output_string o ";;\n";
  output_string o "\n";
  output_string o "(* updates the lexer position to the next line\n";
  output_string o " * (this is used since we skip newlines in the\n";
  output_string o " *  lexer, but we still wish to remember them\n";
  output_string o " *  for proper line positions) *)\n";
  output_string o "let do_newline lb = \n";
  output_string o "   Lexing.new_line lb\n";
  output_string o ";;\n";
  output_string o "\n";
  output_string o "(* dies with a system error s *)\n";
  output_string o "let die_system_error (s : string) =\n";
  output_string o "   output_string stderr s;\n";
  output_string o "   output_string stderr \"\\n\";\n";
  output_string o "   exit 1\n";
  output_string o ";;\n";
  output_string o "\n";
  output_string o "let rec count_newlines s lb = match s with\n";
  output_string o "  | \"\" -> 0\n";
  output_string o "  | _  -> let c = String.sub s 0 1 in\n";
  output_string o "          let cs = String.sub s 1 ((String.length s)-1) in\n";
  output_string o "          if (c=\"\\n\") then (do_newline lb; 1+(count_newlines cs lb))\n";
  output_string o "                      else (count_newlines cs lb)\n";
  output_string o ";;\n";
  output_string o "\n";
  output_string o "let eq_base (a : 'a) (b : 'a) : bool = (a = b) ;;\n";
  output_string o "let rec eq_option (f : 'a -> 'a -> bool) (a : 'a option) (b : 'a option) : bool =\n";
  output_string o "   match (a,b) with\n";
  output_string o "   | (None,None) -> true\n";
  output_string o "   | (Some(a),Some(b)) -> (f a b)\n";
  output_string o "   | _ -> false\n";
  output_string o ";;\n";
  output_string o "let eq_pair (f1 : 'a -> 'a -> bool) (f2 : 'b -> 'b -> bool) ((p1a,p1b) : 'a * 'b) ((p2a,p2b) : 'a * 'b) : bool = ((f1 p1a p2a) && (f2 p1b p2b)) ;;\n";
  output_string o "let eq_list (f : 'a -> 'a -> bool) (l1 : 'a list) (l2 : 'a list) : bool = try List.fold_left2 (fun res l1i l2i -> res && (f l1i l2i)) true l1 l2 with _ -> false;;\n";
  output_string o "\n";
  output_string o "let rec str_option (f : 'a -> string) (o : 'a option) : string =\n";
  output_string o "   match o with\n";
  output_string o "   | None -> \"\"\n";
  output_string o "   | Some(a) -> (f a)\n";
  output_string o ";;\n";
  output_string o "\n";
  output_string o "let rec str_pair (f : 'a -> string) (g : 'b -> string) ((a,b) : ('a * 'b)) : string =\n";
  output_string o "   (f a)^\"\"^\n";
  output_string o "   (g b)\n";
  output_string o ";;\n";
  output_string o "\n";
  output_string o "let rec str_list (f : 'a -> string) (l : 'a list) : string =\n";
  output_string o "   str_list_helper f l true\n";
  output_string o "\n";
  output_string o "and str_list_helper (f : 'a -> string) (l : 'a list) (first : bool) : string =\n";
  output_string o "   match l with\n";
  output_string o "   | [] -> \"\"\n";
  output_string o "   | a::more -> ((if (not first) then \"\" else \"\")^(f a)^(str_list_helper f more false))\n";
  output_string o "let rec str_x_list (f : 'a -> string) (il : 'a list) (comma : string) : string = \n";
  output_string o "    (fst (List.fold_left\n";
  output_string o "    (fun (str,flag) i ->\n";
  output_string o "      (str^(if flag then \"\" else comma)^(f i), false)\n";
  output_string o "    ) (\"\",true) il))\n";
  output_string o ";;\n";
  (match !Flags.utils_code with Some(s(*TODO XXX*),c,px) -> output_string o (str_code_plain c) | _ -> ())

let output_main_code filename o prefix g pname = match g with
| Grammar(pos,(d,dl)) ->
  reset_output filename;
  output_warning_msg pos o "(*\n" " *" " *" " *)";
  output_string o "\n\n";
  output_string o ("open "^(String.capitalize (prefix^"parser"))^";;\n");
  output_string o ("open "^(String.capitalize (prefix^"lexer"))^";;\n");
  output_string o "\n";
  output_string o "let get_ast (i : in_channel) = \n";
  output_string o ("   "^(String.capitalize (prefix^"parser."^pname^""))^" "^(String.capitalize (prefix^"lexer.token"))^" (Lexing.from_channel i)\n");
  output_string o ";;\n"

let generate_makefile_vars o =
   let olevel = (match !Flags.opt_level with
   | None -> ""
   | Some(l) -> " -ccopt -O"^l) in
   let static = (match !Flags.compile_static with
   | false -> ""
   | true -> " -ccopt -static") in
   let debug = (match !Flags.debug_symbols with
   | false -> ""
   | true -> " -p -g") in
   let (command,xo,xa) = (match !Flags.compiler with
   | OCamlC -> ("ocamlc","o","")
   | OCamlOpt -> ("ocamlopt"^olevel^static^debug, "x", "x")
   | OCamlCp -> ("ocamlcp -p a", "o", "")) in
   output_string o ("OCAMLC = "^command^"\n");
   output_string o ("CMO = cm"^xo^"\n");
   output_string o ("CMA = cm"^xa^"a\n")

let output_makefile_code filename o prefix =
  reset_output filename;
  output_warning_msg NoPos o "#\n" "#" "#" "#";
  output_string o "\n\n";
  output_string o "ifndef OCAMLC\n";
  generate_makefile_vars o;
  output_string o "endif\n";
  output_string o (prefix^"main.$(CMO):\t"^prefix^"main.ml "^prefix^"parser.$(CMO) "^prefix^"lexer.$(CMO) "^
                      prefix^"ast.$(CMO) "^prefix^"utils.$(CMO)\n");
  output_string o ("\t\t$(OCAMLC) -c "^prefix^"main.ml\n");
  output_string o ("\n");
  output_string o (""^prefix^"parser.$(CMO):\t"^prefix^"parser.ml "^prefix^"parser.cmi "^
                      prefix^"utils.$(CMO)\n");
  output_string o ("\t\t$(OCAMLC) -c "^prefix^"parser.ml\n");
  output_string o ("\n");
  output_string o (""^prefix^"lexer.$(CMO):\t"^prefix^"lexer.ml "^prefix^"parser.cmi "^
                      prefix^"ast.$(CMO) "^prefix^"utils.$(CMO)\n");
  output_string o ("\t\t$(OCAMLC) -c "^prefix^"lexer.ml\n");
  output_string o ("\n");
  output_string o (""^prefix^"parser.cmi:\t"^prefix^"parser.mli "^prefix^"ast.$(CMO) "^
                      prefix^"utils.$(CMO)\n");
  output_string o ("\t\t$(OCAMLC) -c "^prefix^"parser.mli\n");
  output_string o ("\n");
  output_string o (""^prefix^"ast.$(CMO):\t"^prefix^"ast.ml "^prefix^"utils.$(CMO)\n");
  output_string o ("\t\t$(OCAMLC) -c "^prefix^"ast.ml\n");
  output_string o ("\n");
  output_string o (""^prefix^"parser.ml:\t"^prefix^"parser.mly\n");
  output_string o ("\t\tocamlyacc -v "^prefix^"parser.mly\n");
  output_string o ("\n");
  output_string o (""^prefix^"parser.mli:\t"^prefix^"parser.mly\n");
  output_string o ("\t\tocamlyacc -v "^prefix^"parser.mly\n");
  output_string o ("\n");
  output_string o (""^prefix^"lexer.ml:\t"^prefix^"lexer.mll\n");
  output_string o ("\t\tocamllex "^prefix^"lexer.mll\n");
  output_string o ("\n");
  output_string o (""^prefix^"utils.$(CMO):\t"^prefix^"utils.ml\n");
  output_string o ("\t\t$(OCAMLC) -c "^prefix^"utils.ml\n");
  output_string o ("\n");
  output_string o (prefix^"clean:\t\t\t\n");
  output_string o ("\t\t\trm -rf *.cm* *.mli "^prefix^"parser.ml "^prefix^"lexer.ml\n")

let generate_skeleton_makefile o prefix bin_name grammar_filename =
   generate_makefile_vars o;
   output_string o "\n";
   output_string o "LIBS =";
   Hashtbl.iter (fun k v ->
      output_string o (" "^k^".$(CMA)")
   ) Flags.libs;
   output_string o "\n\n";
   output_string o (bin_name^":\tflags.$(CMO) "^prefix^"utils.$(CMO) "^prefix^"ast.$(CMO) "^
                      prefix^"parser.$(CMO) "^prefix^"lexer.$(CMO) "^prefix^"main.$(CMO) main.$(CMO)\n");
   output_string o ("\t$(OCAMLC) -o "^bin_name^" $(LIBS) flags.$(CMO) "^prefix^"utils.$(CMO) "^
                      prefix^"ast.$(CMO) "^prefix^"parser.$(CMO) "^prefix^"lexer.$(CMO) "^
                      prefix^"main.$(CMO) main.$(CMO)\n");
   output_string o "\n";
   output_string o ("main.$(CMO):\tmain.ml "^prefix^"main.$(CMO) "^prefix^"parser.$(CMO) "^
                      prefix^"lexer.$(CMO) "^
                      prefix^"ast.$(CMO) "^prefix^"utils.$(CMO) flags.$(CMO)\n");
   output_string o "\t$(OCAMLC) -c main.ml\n";
   output_string o "\n";
   output_string o "flags.$(CMO):\tflags.ml\n";
   output_string o "\t$(OCAMLC) -c flags.ml\n";
   output_string o "\n";
   output_string o (prefix^"Makefile:\t"^(grammar_filename)^"\n");
   output_string o ("\turuz2 "^(grammar_filename)^"\n");
   output_string o "\n";
   output_string o ("clean:\t"^prefix^"clean\n");
   (*output_string o ("\trm -rf *.o *.cm* *.mli "^prefix^"main.ml "^prefix^"utils.ml "^
                      prefix^"ast.ml "^
                      prefix^"parser.ml "^prefix^"parser.mly "^prefix^"lexer.ml "^
                      prefix^"lexer.mll "^prefix^"Makefile\n");*)
   output_string o ("\trm -rf *.o *.cm* *.mli "^prefix^"parser.ml "^prefix^"lexer.ml\n");
   output_string o "\n";
   output_string o ("include "^prefix^"Makefile\n")

let generate_skeleton_main o prefix =
   output_string o ("open "^(String.capitalize (prefix^"main"))^";;\n");
   output_string o ("open Flags;;\n");
   output_string o "\n";
   output_string o "let i = parse_command_line () in\n";
   output_string o "let result = get_ast i in\n";
   output_string o "ignore result;\n";
   output_string o "(* Ast.print_grammar 0 result;\n";
   output_string o "print_newline(); *)\n";
   output_string o "exit 0;;\n"

let generate_skeleton_flags o prefix =
   output_string o "(* flag defaults *)\n";
   output_string o "let filename = ref \"\";; (* TODO - this will always be set *)\n";
   output_string o "let out_file = ref (None : string option)\n";
   output_string o "\n";
   output_string o ("let banner_text = \"Welcome to "^prefix^" v. 1.0\";;\n");
   output_string o "let usage_msg = banner_text^\"\\n\"^\n";
   output_string o ("                \"Usage: "^prefix^" [options] <file>\";;\n");
   output_string o "\n";
   output_string o "(* parse the command-line arguments *)\n";
   output_string o "let args = Arg.align [\n";
   output_string o "   (\"-o\",        Arg.String(fun x -> out_file := Some(x)),\n";
   output_string o "                    \"<file> Location for the result\");\n";
   output_string o "];;\n";
   output_string o "\n";
   output_string o "let error_usage_msg () =\n";
   output_string o "   Arg.usage args usage_msg;\n";
   output_string o "   exit 1\n";
   output_string o ";;\n";
   output_string o "\n";
   output_string o "(* dies with a system error s *)\n";
   output_string o "let die_system_error (s : string) =\n";
   output_string o "   output_string stderr s;\n";
   output_string o "   output_string stderr \"\\n\";\n";
   output_string o "   exit 1\n";
   output_string o ";;\n";
   output_string o "\n";
   output_string o "let parse_command_line () : in_channel =\n";
   output_string o "   let f_set = ref false in\n";
   output_string o "   Arg.parse args (fun x -> f_set := true; filename := x) banner_text;\n";
   output_string o "   (* use the command-line filename if one exists, otherwise use stdin *)\n";
   output_string o "   match !f_set with\n";
   output_string o "   | false -> error_usage_msg ()\n";
   output_string o "   | true -> (\n";
   output_string o "      try (open_in !filename)\n";
   output_string o "      with _ -> die_system_error (\"can't read from file: \"^(!filename))\n";
   output_string o "   )\n";
   output_string o ";;\n"

let generate_skeleton dir prefix bin_name grammar_filename =
   let makefile_path = dir^"Makefile" in
   if not (Sys.file_exists makefile_path) then (
      let file = open_out makefile_path in
      generate_skeleton_makefile file prefix bin_name grammar_filename;
      close_out file
   );
   let main_path = dir^"main.ml" in
   if not (Sys.file_exists main_path) then (
      let file = open_out main_path in
      generate_skeleton_main file prefix;
      close_out file
   );
   let flags_path = dir^"flags.ml" in
   if not (Sys.file_exists flags_path) then (
      let file = open_out flags_path in
      generate_skeleton_flags file prefix;
      close_out file
   )

let output_code dir prefix g bin_name grammar_filename gr =
  let dir_prefix = (match dir with None -> "" | Some(d) -> d^Filename.dir_sep) in
  let fn = prefix^"parser.mly" in
  let o = open_out (dir_prefix^fn) in
  let (start_name,keywords) = output_parser_code fn o prefix g gr in
  close_out o;
  let fn = prefix^"lexer.mll" in
  let o = open_out (dir_prefix^fn) in
  output_lexer_code fn o prefix g keywords;
  close_out o;
  let fn = prefix^"ast.ml" in
  let o = open_out (dir_prefix^fn) in
  output_ast_code fn o prefix g;
  close_out o;
  let fn = prefix^"utils.ml" in
  let o = open_out (dir_prefix^fn) in
  output_utils_code fn o prefix g;
  close_out o;
  let fn = prefix^"main.ml" in
  let o = open_out (dir_prefix^fn) in
  output_main_code fn o prefix g start_name;
  close_out o;
  let fn = prefix^"Makefile" in
  let o = open_out (dir_prefix^fn) in
  output_makefile_code fn o prefix;
  close_out o;
  (* generate the skeleton files *)
  generate_skeleton dir_prefix prefix bin_name grammar_filename
