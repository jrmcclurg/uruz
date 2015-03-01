(* TODO XXX - pretty-printing of string/char literals needs to print the quotes *)
(* TODO XXX - emit normalize_ and get_pos_ functions *)
(* TODO XXX - maybe disallow "_" in identifiers *)

open Bootstrap_ast
open Bootstrap_utils
open Flags

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

let modify_code (p : pos_t) (cd : code option) f (default : string) : code option =
(*match cd with Some(Code(p,c)) -> Some(Code(p,f c)) | _ -> cd*)
Some(Code(p,f (match cd with Some(Code(p,c)) -> c | _ -> default)))

(* HANDLE PROPERTIES *)

let rec handle_props (g : grammar_t) : (grammar_t*int) = match g with
| Grammar(pos,(d,dl)) ->
  let (dl2,count) = List.fold_left (fun (acc,index) d -> (match d with
    | PropDecl(p,name,value) -> (
      match (get_symbol name,value) with
      | ("default_production_type",StringVal(p,s)) -> Flags.def_prod_type := str_to_rule_type p s
      | ("default_production_name",StringVal(p,s)) -> Flags.def_prod_name := s
      | ("parameter_name",StringVal(p,s)) -> Flags.param_name := s
      | ("type_name",StringVal(p,s)) -> Flags.type_name := s
      | ("parser_code",CodeVal(p,(c,cl))) -> () (* TODO XXX *)
      | ("lexer_code",CodeVal(p,(c,cl))) -> () (* TODO XXX *)
      | ("ast_code",CodeVal(p,(c,cl))) -> () (* TODO XXX *)
      | ("util_code",CodeVal(p,(c,cl))) -> () (* TODO XXX *)
      | _ -> die_error p "invalid property name or type"
      );
      acc
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

let flatten_list f l defname deftyp nesting code_table len f2 =
let (l2,prods,_) = List.fold_left (fun (l2,prods,index) x ->
  let (x2,prods2) = f x defname deftyp (index::nesting) code_table ((f2 x) && len=1) in
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
  let (patl2,prods) = flatten_list flatten_pattern patl defname deftyp nesting code_table (List.length patl) (fun x -> true) in
  (Production(ps,o2,patl2),prods)

and flatten_pattern (p : pattern_t) (defname : symb option) (deftyp : rule_type option) (nesting : int list) (code_table : code_hashtbl) (is_singleton : bool) : (pattern_t*decl_t list) = match p with
| Pattern(p,(al,xo)) ->
  (*let len = (match xo with Some(name,(opts,(cd,Some(ty)))) -> 2 | Some(name,(opts,(Some(cd),ty))) -> 2 | _ -> List.length al) in*)
  let len = (match xo with Some(_) -> 2 | _ -> List.length al) in
  let (al2,prods) = flatten_list flatten_annot_atom al defname deftyp nesting code_table len
    (fun x -> match x with QuantAnnotAtom(_,_,_) -> is_singleton | _ -> true) in
  (Pattern(p,(al2,match xo with Some(n,o) -> Some(n,(flatten_opt_list p o deftyp nesting code_table)) | None -> None)),prods)

and flatten_annot_atom (an : annot_atom_t) (defname : symb option) (deftyp : rule_type option) (nesting : int list) (code_table : code_hashtbl) (is_singleton : bool) : (annot_atom_t*decl_t list) = match an with
| SingletonAnnotAtom(p,a) -> let (a2,prods) = flatten_atom a defname deftyp nesting code_table is_singleton in (a2,prods)
| QuantAnnotAtom(p,an,q) ->
  let (a2,prods) = flatten_annot_atom an defname deftyp (if is_singleton then nesting else (!Flags.def_prod_index::nesting)) code_table false in
  let y = QuantAnnotAtom(p,a2,q) in
  if is_singleton || (is_processing_lexer deftyp) then (y,prods)
  else
    let name = Flags.get_def_prod_name defname nesting in
    (SingletonAnnotAtom(p,IdentAtom(p,name)),
    (ProdDecl(p,Production(p,((Some(Flags.get_def_prod_type deftyp)),(Some(name),([],(None,None)))),
      [Pattern(p,([y],None))])))::prods)
| OptAnnotAtom(p,an,(o,x)) ->
  if is_processing_lexer deftyp then
    die_error p "lexer productions can only contain annotations on the left-hand-side (i.e. applied to the entire production)";
  let (a2,prods) = flatten_annot_atom an defname deftyp (if is_singleton then nesting else (!Flags.def_prod_index::nesting)) code_table false in
  if is_singleton then (OptAnnotAtom(p,a2,(o,x)),prods)
  else
    let name = Flags.get_def_prod_name defname nesting in
    (SingletonAnnotAtom(p,IdentAtom(p,name)),
    (ProdDecl(p,Production(p,((Some(Flags.get_def_prod_type deftyp)),(Some(name),([],(None,None)))),
      [Pattern(p,([OptAnnotAtom(p,a2,(o,x))],None))])))::prods)

and is_inlined p (ol,(co,tyo)) : (bool * (opt_t list * (code option * typ_t option))) =
  let (is_inl, ol2) = opt_list_contains ol inline_kw (BoolVal(NoPos,true)) in
  (is_inl, ((if is_inl then (ol2@[ValOption(p,Some(auto_kw),BoolVal(p,false))]) else ol2),(co,tyo)))

and flatten_atom (a : atom_t) (defname : symb option) (deftyp : rule_type option) (nesting : int list) (code_table : code_hashtbl) (is_singleton : bool) : (annot_atom_t*decl_t list) = match a with
| IdentAtom(p,_) ->
  if is_processing_lexer deftyp then
    die_error p "lexer productions cannot reference other productions";
  (SingletonAnnotAtom(p,a),[])
| ProdAtom(p,Production(p2,(kwo,(nameo,ol)),patl)) ->
  let name, nesting, defname = (match nameo with
  | Some(name) -> 
    if is_processing_lexer deftyp then die_error p2 "nested lexer productions cannot have names"
    else (name, [], Some(name))
  | None -> (Flags.get_def_prod_name defname nesting, nesting, defname)
  ) in
  let (patl2,prods) = flatten_list flatten_pattern patl defname (match kwo with None -> deftyp | _ -> kwo) nesting code_table (List.length patl) (fun x -> true) in
  if is_processing_lexer deftyp then (SingletonAnnotAtom(p,ProdAtom(p,Production(p2,(Some(Lexer),(None,flatten_opt_list p2 ol deftyp nesting code_table)),patl2))),[]) (* TODO XXX *)
  else (
    let (is_inl, ol) = is_inlined p ol in
    let result = Production(p2,((match kwo with None -> Some(Flags.get_def_prod_type deftyp) | _ -> kwo),
      (Some(name),(let (x,y) = flatten_opt_list p2 ol deftyp nesting code_table in (x,y)))),patl2) in
    if false(*TODO*) && is_singleton then (SingletonAnnotAtom(p,ProdAtom(p,result)),prods)
    else ((if is_inl then
    (*OptAnnotAtom(p,SingletonAnnotAtom(p,IdentAtom(p,name)),([ValOption(p,Some(inline_kw),BoolVal(p,true))],(None,None)))*)
    OptAnnotAtom(p,SingletonAnnotAtom(p,IdentAtom(p,name)),([(*ValOption(p,Some(inline_kw),BoolVal(p,true))*)],(None,Some(CompoundType(p,AbstrType(p,IdentName(p,name),[SingletonConstrType(p,SimpleType(p,AnyType(p)))]))))))
      else SingletonAnnotAtom(p,IdentAtom(p,name))),(ProdDecl(p2,result))::prods)
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
| EofAtom(p)
| CharsetAtom(p,_,_)
| RecurAtom(p,_,_)
| StringAtom(p,_) -> (SingletonAnnotAtom(p,a),[])

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
  let (x,(b,o)) = (List.fold_left (fun (acc,(acc2,acc3)) x -> let (y,(b,o)) = elim_pattern x name in (List.rev_append y acc, ((b||acc2), (match acc3 with None -> o | _ -> acc3)))) ([],(false,None)) patl) in
  Production(ps,(r,(Some(name),(opts,((if b then Some(Code(ps,"List.rev x")) else cd),
  (match o with Some(kw) -> Some(mk_compound_type ps (AnyType(ps)) kw) | _ -> ty))))),List.rev x)
| Production(ps,_,_) -> die_error ps "production did not acquire a name"

and elim_pattern (pa : pattern_t) (prod_name : symb) : (pattern_t list * (bool*symb option)) = match pa with
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
  ([Pattern(p,([OptAnnotAtom(p2,a,(opts,(None,None)))],Some(None,([],(cd,ty)))))], (false,None))
(*| Pattern(p,([OptAnnotAtom(p2,a,(opts1,(cd,ty)))],Some(name,(opts2,(None,None))))) ->
  (* TODO XXX ^^ combine_opt_list opts1 opts2 *)
  [Pattern(p,([OptAnnotAtom(p2,a,(opts1,(None,None)))],Some(name,(opts2,(cd,ty)))))]*)
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
    mark        (* mark used in topological sort *) *
    bool        (* is_def *) *
    pos_t       (* definition location *)
    (*production_t*) (* TODO XXX *)
  ) Hashtbl.t

(* Tarjan's algorithm - returns a topological sort of the strongly-connected components *)
(* http://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm *)
let rec topo_sort (graph : simple_graph) (*(vertices : IntSet.t)*) : (int list) list =
  let stack = ((Stack.create ()) : int Stack.t) in
  let result = fst (Hashtbl.fold (fun k (childs,m,_,_) (res,index) ->
    if true(*(IntSet.mem k vertices)*) then topo_dfs k res graph index stack else (res,index)
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

let rec build_def_graph_grammar (g : grammar_t) (count : int) : simple_graph = match g with
| Grammar(pos,(d,dl)) ->
  let graph = (Hashtbl.create (10*count)(*TODO XXX - num?*) : simple_graph) in
  List.iter (fun d -> (match d with
    | ProdDecl(p,Production(p2,(_,(None,_)),patl)) -> die_error p2 "production is not named"
    | ProdDecl(p,Production(p2,(_,(Some(name),_)),patl)) ->
      (*Printf.printf ">>> processing name: '%s'\n%!" (get_symbol name);*)
      let x = (try let (set,m,is_def,ps) = Hashtbl.find graph name in
        if is_def then die_error p2 ("multiple definition of '"^(get_symbol name)^"'") else (set,m,true,p2)
        with Not_found -> (IntSet.empty,None,true,p2)) in
      Hashtbl.replace graph name x;
      List.iter (fun pat -> build_def_graph_pattern pat graph name) patl
    | _ -> ())
  ) (d::dl);
  graph

and build_def_graph_pattern (p : pattern_t) (g : simple_graph) (parent : symb) : unit = match p with
| Pattern(p,(anl,x)) ->
  List.iter (fun an -> build_def_graph_annot_atom an g parent) anl

and build_def_graph_annot_atom (an : annot_atom_t) (g : simple_graph) (parent : symb) : unit = match an with
| SingletonAnnotAtom(p,a) -> build_def_graph_atom a g parent
| QuantAnnotAtom(p,an,q) -> build_def_graph_annot_atom an g parent
| OptAnnotAtom(p,an,o) -> build_def_graph_annot_atom an g parent

and build_def_graph_atom (a : atom_t) (g : simple_graph) (parent : symb) : unit = match a with
| IdentAtom(p,id) -> 
  let (set,m,is_def,ps) = (try Hashtbl.find g parent with Not_found -> (IntSet.empty,None,false,p)) in
  Hashtbl.replace g parent (IntSet.add id set,m,is_def,ps);
  let x = (try Hashtbl.find g id with Not_found -> (IntSet.empty,None,false,p)) in
  Hashtbl.replace g id x;
| ProdAtom(p,Production(p2,_,pl)) ->
  List.iter (fun x -> build_def_graph_pattern x g parent) pl
| _ -> ()

let get_sorted_defs (result : grammar_t) (count : int) : ((symb*pos_t) list) =
  let graph = build_def_graph_grammar result count in
  let comps = topo_sort graph in
  let x = List.rev_map (fun comp -> match comp with
    | [] -> failwith "topological sort returned empty connected component"
    | a::more ->
      let (_,_,_,ps) = (try Hashtbl.find graph a with Not_found -> (IntSet.empty,None,false,NoPos) (*TODO XXX fail?*)) in
      if more=[] then (a,ps) else die_error ps ("cyclic defintion: "^(str_x_list get_symbol comp ", "))
  ) comps in
  x

(*******************************************)
(** ????????????                          **)
(*******************************************)

let placeholder_char = '*'

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

let val_to_atom (v : value_t) : atom_t = match v with
| StringVal(ps,str) -> StringAtom(ps,str)
| CharVal(ps,c) -> CharsetAtom(ps,SingletonCharset(ps,c),None)
| _ -> failwith ("could not convert value '"^(str_value_t v)^"' to atom")

let rec strip_lexer_grammar (g : grammar_t) (count : int) : (grammar_t * (symb,production_t) Hashtbl.t) = match g with
| Grammar(pos,(d,dl)) ->
  let the_list = (d::dl) in
  let table = Hashtbl.create count in
  let dl2 = List.rev_map (fun x -> strip_lexer_decl x table) the_list in
  let l = List.rev dl2 in
  (Grammar(pos,(List.hd l,List.tl l)), table)

and strip_lexer_decl (d : decl_t) (table : (symb,production_t) Hashtbl.t) : decl_t = match d with
| ProdDecl(p,(Production(p2,((Some(Lexer),(so,ol)) as name),pl) as prod)) ->
  let sym = (match so with
  | Some(s) -> s
  | None -> die_error p2 "un-named lexer production") in
  Hashtbl.replace table sym prod;
  let v = val_to_atom (get_placeholder_value_production prod) in
  ProdDecl(p,Production(p2,name,[Pattern(p2,([SingletonAnnotAtom(p2,v)],None))]))
| _ -> d

(*******************************************)
(** TYPECHECKING                          **)
(*******************************************)

type prod_hashtbl = (symb,production_t * typ_t option) Hashtbl.t

(* TODO XXX - need to handle NoType properly throughout!! *)

(* TODO XXX - make sure to add get_current_position when generating the cast *)

let typecast (inner : bool) (co : code option) (old_types : typ_t list) (new_type : typ_t) : code option =
let fail p = die_error p ("don't know how to cast type ("^(str_x_list str_typ_t old_types "*")^") to "^(str_typ_t new_type)) in
match co with
| Some(_) -> co
| None -> (
match (old_types,new_type) with
| ([SimpleType(p,TokenType(_))],SimpleType(_,TokenType(_)))
| ([SimpleType(p,UnitType(_))],SimpleType(_,UnitType(_))) -> None
| ([SimpleType(p,IdentType(_,[kw1]))],SimpleType(_,IdentType(_,[kw2]))) ->
  if kw1=kw2 then Some(Code(p,if inner then "$1" else !Flags.param_name)) else (* TODO XXX *)
  (try Some(Code(p,(if inner then ("let "^(!Flags.param_name)^" = $1 in ") else "")^(Hashtbl.find Flags.typecast_table (kw1,kw2))^" "^(!Flags.param_name))) with Not_found -> fail p)
(* TODO XXX ... *)
| (_,SimpleType(p,_))
| (_,CompoundType(p,_)) -> fail p
)

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
| (CompoundType(p,AbstrType(p2,an1,cl1)),CompoundType(_,AbstrType(_,an2,cl2))) ->
  (*(try CompoundType(p,AbstrType(p2,unify_abstr_name an1 an2,List.rev (List.rev_map2 (fun c1 c2 -> unify_constr_type c1 c2) cl1 cl2)))
  with _ -> fail p)*)
  SimpleType(p,IdentType(p,[auto_name]))
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
| (InstConstrType(p,ct1,s1),InstConstrType(p2,ct2,s2)) ->
  if s1=s2 then InstConstrType(p,unify_constr_type ct1 ct2 auto_name,s1) else fail p
| (SingletonConstrType(p,_),InstConstrType(_,_,_))
| (InstConstrType(p,_,_),SingletonConstrType(_,_)) -> fail p

and unify_abstr_name (an1 : abstr_name_t) (an2 : abstr_name_t) : abstr_name_t =
let fail p = die_error p (Printf.sprintf "could not unify type %s with %s" (str_abstr_name_t an1) (str_abstr_name_t an2)) in
match (an1,an2) with
| (AnyName(p),_) -> an2
| (_,AnyName(p)) -> an1
| (IdentName(p,s1),IdentName(p2,s2)) ->
  if s1=s2 then an1 else fail p

let rec infer_type_annot_atom (a : annot_atom_t) (prod_table : prod_hashtbl) : (typ_t*annot_atom_t) =
match a with
| SingletonAnnotAtom(p,EmptyAtom(p2)) ->
  let t = SimpleType(p2,NoType(p2)) in (t,OptAnnotAtom(p,a,([],(None,Some(t)))))
| SingletonAnnotAtom(p,EofAtom(p2)) ->
  let t = SimpleType(p2,NoType(p2)) in (t,OptAnnotAtom(p,a,([],(None,Some(t)))))
| SingletonAnnotAtom(p,StringAtom(p2,s)) ->
  let t = SimpleType(p2,IdentType(p2,[string_kw])) in (t,OptAnnotAtom(p,a,([],(None,Some(t)))))
| SingletonAnnotAtom(p,IdentAtom(p2,name)) ->
  let typo = (try let (_,x) = Hashtbl.find prod_table name in x with Not_found ->
    die_error p2 ("wasn't able to typecheck production: "^(get_symbol name))
  ) in
  let t = (match typo with None -> SimpleType(p2,AnyType(p2)) | Some(t) -> t) in
  (t,OptAnnotAtom(p,a,([],(None,Some(t)))))
| SingletonAnnotAtom(p,CharsetAtom(p2,cs,cso)) ->
  let t = SimpleType(p2,IdentType(p2,[string_kw])) in
  (t,OptAnnotAtom(p,a,([],(None,Some(t)))))
| SingletonAnnotAtom(p,RecurAtom(p2,s1,s2)) ->
  let t = SimpleType(p2,IdentType(p2,[string_kw])) in
  (t,OptAnnotAtom(p,a,([],(None,Some(t)))))
| OptAnnotAtom(p,a,(ol,(None,None))) ->
  infer_type_annot_atom a prod_table
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

and infer_type_production (pr : production_t) (prod_table : prod_hashtbl) : (typ_t*production_t) =
match pr with
| Production(ps,(rt,(name,(ol,(cd,Some(ty))))),patl) -> (ty,pr) (* TODO XXX *)
| Production(ps,(rt,(name,(ol,(cd,ty)))),patl) -> (SimpleType(ps,AnyType(ps)),pr)

let val_to_atom (v : value_t) : (annot_atom_t*typ_t) =
match v with
| StringVal(p,s) -> (SingletonAnnotAtom(p,StringAtom(p,s)),SimpleType(p,IdentType(p,[string_kw])))
| CharVal(p,c) -> (SingletonAnnotAtom(p,CharsetAtom(p,SingletonCharset(p,c),None)),SimpleType(p,IdentType(p,[string_kw])))
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

let get_auto_type_name (prod_name : symb) : symb =
  let str = get_symbol prod_name in
  (*let c = String.get str 0 in*)
  let str = str(*(if (Char.lowercase c)<>c then ("_"^str) else str)*)^(!Flags.auto_type_suffix) in
  add_symbol str

let is_auto_type (t : typ_t) (prod_name : symb) : bool =
match t with
| CompoundType(_,AbstrType(_)) -> true
| SimpleType(_,IdentType(_,[kw])) ->
  let str = get_symbol prod_name in
  kw=(add_symbol (str^(!Flags.auto_type_suffix)))
| _ -> false

let is_no_type (t : typ_t) : bool =
match t with
| SimpleType(_,NoType(_)) -> true
| _ -> false

let rec is_finalized_typ (t : typ_t) : bool =
match t with
| SimpleType(_,AnyType(_)) -> false
| SimpleType(_,VarType(_)) -> false
| SimpleType(_,_) -> true
| CompoundType(_,CommaType(_,cll)) -> List.for_all (fun cl -> List.for_all is_finalized_constr_type cl) cll
| CompoundType(_,AbstrType(_,an,cl)) -> List.for_all is_finalized_constr_type cl

and is_finalized_constr_type (ct : constr_type_t) : bool =
match ct with
| SingletonConstrType(_,t) -> is_finalized_typ t
| InstConstrType(_,ct,_) -> is_finalized_constr_type ct

let typecheck (g : grammar_t) (comps : (symb*pos_t) list) (count : int) : grammar_t = match g with
| Grammar(pos,(d,dl)) ->
  let prod_table = (Hashtbl.create count : prod_hashtbl) in
  (* set up a map containing all productions *)
  List.iter (fun d ->
    match d with
    (* NOTE - all productions should be named at this point *)
    | ProdDecl(p,(Production(p2,(rto,(Some(name),ol)),pl) as prod)) ->
      Hashtbl.replace prod_table name (prod,None);
      Printf.printf "adding: %s\n%!" (get_symbol name)
    | _ -> ()
  ) (d::dl);
  Printf.printf "----------------------\n";
  let prods = List.rev (List.rev_map (fun (name,ps) ->
    let ((Production(p,(rt,(name1,(ol1,(cd1,ty1)))),pl) as prod),t) =
      (try Hashtbl.find prod_table name
      with Not_found -> die_error ps ("could not find production '"^(get_symbol name)^"'")) in
    let is_lexer = (match rt with (Some(Lexer)) -> true | _ -> false) in
    let auto_name = get_auto_type_name name in
    let pl = (if is_lexer then
      let (a,ty) = val_to_atom (get_placeholder_value_production prod) in
      [Pattern(p,([a],Some(None,([],(None,Some(ty))))))] else pl) in
    let (pl2,types,ty) = (List.fold_left (fun (acc,acc2,tyo) (Pattern(p,(al,xo))) ->
      let temp = (List.rev_map (fun a -> (infer_type_annot_atom a prod_table)) al) in
      let (al2,tys) = List.fold_left (fun (acc1,acc2) (ty,a) -> ((a::acc1),(ty::acc2))) ([],[]) temp in
      let (tyo2,xo2) = (match xo with
      | Some(name,(opts,(cd,ty))) -> let ty = replace_vars_typ_opt tys ty in (
        (match (ty,tyo) with
        | (Some(ty),Some(ty2)) -> Some(unify_typ ty ty2 auto_name)
        | (_,Some(ty2)) -> Some(ty2)
        | (Some(ty),_) -> Some(ty)
        | (None,None) -> None
      ),Some(name,(opts,(cd,ty))))
      | _ -> (tyo,xo)) in
      ((Pattern(p,(al2,xo2)))::acc,tys::acc2,tyo2)
    ) ([],[],None) pl) in
    (*let pl2 = List.rev pl2 in*)
    let (is_auto,ty) = (match ty with
    | None -> (true,SimpleType(p,IdentType(p,[auto_name])))
    | Some(t) -> let b = is_auto_type t name in (b,if b then SimpleType(p,IdentType(p,[auto_name])) else t)) in
    (*let ty = (match ty with CompoundType(_,AbstrType(_,_,_)) -> SimpleType(p,IdentType(p,[auto_name])) | _ -> ty) in*)
    let (pl2,_) = List.fold_left2 (fun (acc,index) (Pattern(p,(al,xo))) tys ->
      let str = get_symbol name in
      let kw_name = add_symbol (str^"_"^(string_of_int index)) in
      let mk_ty nm = (if is_auto then
        (CompoundType(p,AbstrType(p,
        IdentName(p,(
          match nm with
          | Some(kw) -> kw
          | _ -> kw_name
        )),
        (*List.rev (List.rev_map (fun t -> SingletonConstrType(p,t)) tys))))*)
        List.rev (List.fold_left (fun acc t -> if is_no_type t then acc else SingletonConstrType(p,t)::acc) [] tys)
        )))
        else ty
      ) in
      let xo2 = (match xo with
      | Some(name,(opts,(cd,Some(CompoundType(_,AbstrType(_,_,_)) as ct)))) ->
        Some((match name with None -> Some(kw_name) | _ -> name),(opts,(typecast true cd tys ct,Some(ct))))
      | Some(name,(opts,(cd,_))) ->
        let new_ty = mk_ty name in
        Some((match name with None -> Some(kw_name) | _ -> name),(opts,(typecast true cd tys new_ty,Some(new_ty))))
      | None ->
        let new_ty = mk_ty None in
        Some(Some(kw_name),([],(typecast true None tys new_ty,Some(new_ty))))) in
      (((Pattern(p,(al,xo2)))::acc),index-1)
    ) ([],(List.length pl2)-1) pl2 types in
    Printf.printf "processing:\n---------\n%s\n--------\nunified = %s\nauto name = %s\nis auto = %b\n\n%!"
      (str_production_t prod)
      (str_typ_t ty)
      (get_symbol auto_name)
      is_auto
      ;
    (*Printf.printf "processing:\n--------\n%s\n--------\nunified = %s\nplaceholder = %s\ntype = %s\n\n%!"
      (str_production_t prod)
      (str_option str_typ_t (List.fold_left (fun acc (Pattern(_,(_,xo))) ->
      match xo with Some(name,(opts,(cd,ty))) -> (match (ty,acc) with (Some(ty),Some(ty2)) -> Some(unify_typ ty ty2) | (_,Some(ty2)) -> Some(ty2) | (Some(ty),_) -> Some(ty) | (None,None) -> None) | _ -> acc
      ) None pl))
      (match rt with (Some(Lexer)) -> (str_value_t (get_placeholder_value_production prod)) | _ -> "[not lexer]")
      (str_x_list (fun (Pattern(_,(al,xo))) -> str_x_list (fun (ty,a) -> "{"^(str_annot_atom_t a)^" => "^(str_typ_t ty)^"}")
      (List.map (fun x -> (if (not is_lexer) then infer_type_annot_atom x prod_table
      else (SimpleType(NoPos,NoType(NoPos)),x))) al) ", ") pl "; ")*)
    (* compute the overall type of the production *)
    let ty1 = (match (ty1,ty) with
    | (None,_) -> ty
    | (Some(ty1),ty2) -> if is_finalized_typ ty1 then (ty1) else (unify_typ ty1 ty2 auto_name)) in
    let result = Production(p,(rt,(name1,(ol1,(typecast false cd1 [ty] ty1,Some(ty1))))),pl2) in
    (* add production type to the table *)
    Hashtbl.replace prod_table name (result,Some(ty1));
    ProdDecl(p,result)
  ) comps) in
  let l = (List.filter (fun x -> match x with ProdDecl(_,_) -> false | _ -> true) (d::dl)) in
  let l = List.rev_append (List.rev l) prods in
  Grammar(pos,(List.hd l, List.tl l))
