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

(* HANDLE PROPERTIES *)

let rec handle_props (g : grammar_t) : (grammar_t*int) = match g with
| Grammar(pos,(d,dl)) ->
  let (dl2,count) = List.fold_left (fun (acc,index) d -> (match d with
    | PropDecl(p,name,value) -> (
      match (get_symbol name,value) with
      | ("default_production_type",StringVal(p,s)) -> Flags.def_prod_type := str_to_rule_type p s
      | ("default_production_name",StringVal(p,s)) -> Flags.def_prod_name := s
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
| Pattern(p,(opts,ty),al) -> Pattern(p,(inline_opt_list opts code_table,ty),List.rev (List.rev_map (inline_annot_atom code_table) al))

and inline_annot_atom (code_table : code_hashtbl) (an : annot_atom_t) : annot_atom_t = match an with
| SingletonAnnotAtom(p,a,(opts,ty)) -> SingletonAnnotAtom(p,inline_atom code_table a,(inline_opt_list opts code_table,ty))
| QuantAnnotAtom(p,an,q,(opts,ty)) -> QuantAnnotAtom(p,inline_annot_atom code_table an,q,(inline_opt_list opts code_table,ty))

and inline_atom (code_table : code_hashtbl) (a : atom_t) : atom_t = match a with
| ProdAtom(p,prod) -> ProdAtom(p,inline_production code_table prod)
| _ -> a

(* FLATTEN PRODUCTIONS *)

let flatten_list f l defname deftyp nesting code_table =
let len = List.length l in
let (l2,prods,_) = List.fold_left (fun (l2,prods,index) x ->
  let (x2,prods2) = f x defname deftyp (index::nesting) code_table (len=1) in
  ((x2::l2), List.rev_append prods2 prods, index+1)
) ([],[], !Flags.def_prod_index) l in
(List.rev l2, List.rev prods)

let flatten_opt_list (p : pos_t) ((ol,tyo) : (opt_t list*typ_t option)) (deftyp : rule_type option) (nesting : int list)
(code_table : code_hashtbl) (check_len : bool) : (opt_t list*typ_t option) =
  let nesting_len = List.length nesting in
  let ol_len = (List.length ol)+(match tyo with None -> 0 | _ -> 1) in
  if (if check_len then ol_len else nesting_len) > (if check_len then 0 else 1) && is_processing_lexer deftyp then
    die_error p "nested lexer productions cannot have names or annotations";
  (ol,tyo)

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
  | (None,(None,ol)) -> (Some(get_def_prod_type deftyp),(Some(get_def_prod_name defname nesting),([],None)))
  | (None,(Some(name),ol)) -> (Some(get_def_prod_type deftyp),(Some(name),flatten_opt_list ps ol deftyp nesting_old code_table false))
  | (Some(kw),(None,ol)) -> (Some(kw),(Some(get_def_prod_name defname nesting),flatten_opt_list ps ol deftyp nesting_old code_table false))
  | (Some(kw),(Some(name),ol)) -> (Some(kw),(Some(name),flatten_opt_list ps ol deftyp nesting_old code_table false))
  ) in
  let (patl2,prods) = flatten_list flatten_pattern patl defname deftyp nesting code_table in
  (Production(ps,o2,patl2),prods)

and flatten_pattern (p : pattern_t) (defname : symb option) (deftyp : rule_type option) (nesting : int list) (code_table : code_hashtbl) (is_singleton : bool) : (pattern_t*decl_t list) = match p with
| Pattern(p,opts,al) ->
  let opts2 = flatten_opt_list p opts deftyp nesting code_table true in
  let (al2,prods) = flatten_list flatten_annot_atom al defname deftyp nesting code_table in
  (Pattern(p,opts2,al2),prods)

(* TODO XXX - fix this *)
and flatten_annot_atom (an : annot_atom_t) (defname : symb option) (deftyp : rule_type option) (nesting : int list) (code_table : code_hashtbl) (is_singleton : bool) : (annot_atom_t*decl_t list) = match an with
| SingletonAnnotAtom(p,a) -> let (a2,prods) = flatten_atom a defname deftyp nesting code_table is_singleton in (SingletonAnnotAtom(p,a2),prods)
| QuantAnnotAtom(p,an,q) ->
  let (a2,prods) = flatten_annot_atom an defname deftyp (if is_singleton then nesting else (!Flags.def_prod_index::nesting)) code_table false in
  if is_singleton then (QuantAnnotAtom(p,a2,q),prods)
  else
    let name = Flags.get_def_prod_name defname nesting in
    (SingletonAnnotAtom(p,IdentAtom(p,name)),(ProdDecl(p,Production(p,((Some(Flags.get_def_prod_type deftyp)),(Some(name),[])),
      [Pattern(p,[],[QuantAnnotAtom(p,a2,q)])])))::prods)
(* TODO XXX - need to flatten these as well *)
| OptAnnotAtom(p,an,o) ->
  if is_processing_lexer deftyp then
    die_error p "lexer productions can only contain annotations on the left-hand-side (i.e. applied to the entire production)";
  let is_singleton = (match o with CodeOption(_,Some(_),_) -> true | _ -> is_singleton) in
  let (a2,prods) = flatten_annot_atom an defname deftyp (if is_singleton then nesting else (!Flags.def_prod_index::nesting)) code_table false in
  if is_singleton then (OptAnnotAtom(p,a2,o),prods)
  else
    let name = Flags.get_def_prod_name defname nesting in
    (SingletonAnnotAtom(p,IdentAtom(p,name)),(ProdDecl(p,Production(p,((Some(Flags.get_def_prod_type deftyp)),(Some(name),[])),
      [Pattern(p,[],[OptAnnotAtom(p,a2,o)])])))::prods)

and flatten_atom (a : atom_t) (defname : symb option) (deftyp : rule_type option) (nesting : int list) (code_table : code_hashtbl) (is_singleton : bool) : (atom_t*decl_t list) = match a with
| IdentAtom(p,_) ->
  if is_processing_lexer deftyp then
    die_error p "lexer productions cannot reference other productions";
  (a,[])
| ProdAtom(p,Production(p2,(kwo,(None,ol)),patl)) ->
  let name = Flags.get_def_prod_name defname nesting in
  let (patl2,prods) = flatten_list flatten_pattern patl defname (match kwo with None -> deftyp | _ -> kwo) nesting code_table in
  if is_processing_lexer deftyp then (ProdAtom(p,Production(p2,(Some(Lexer),(None,ol)),patl2)),[]) (* TODO XXX *)
  else (IdentAtom(p,name),(ProdDecl(p2,Production(p2,((match kwo with None -> Some(Flags.get_def_prod_type deftyp) | _ -> kwo),(Some(name),([],None))),patl2)))::prods)
| ProdAtom(p,Production(p2,(kwo,(Some(name),ol)),patl)) -> 
  let (patl2,prods) = flatten_list flatten_pattern patl (Some(name)) (match kwo with None -> deftyp | _ -> kwo) [] code_table in
  if is_processing_lexer deftyp then die_error p2 "nested lexer productions cannot have names"
  else (IdentAtom(p,name),(ProdDecl(p2,Production(p2,((match kwo with None -> Some(Flags.get_def_prod_type deftyp) | _ -> kwo),(Some(name),flatten_opt_list p2 ol deftyp nesting code_table false)),patl2)))::prods)
| _ -> (a,[])

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
| Pattern(p,opts,anl) ->
  List.iter (fun an -> build_def_graph_annot_atom an g parent) anl

and build_def_graph_annot_atom (an : annot_atom_t) (g : simple_graph) (parent : symb) : unit = match an with
| SingletonAnnotAtom(p,a,o) -> build_def_graph_atom a g parent
| QuantAnnotAtom(p,an,q,o) -> build_def_graph_annot_atom an g parent

and build_def_graph_atom (a : atom_t) (g : simple_graph) (parent : symb) : unit = match a with
| IdentAtom(p,id) -> 
  let (set,m,is_def,ps) = (try Hashtbl.find g parent with Not_found -> (IntSet.empty,None,false,p)) in
  Hashtbl.replace g parent (IntSet.add id set,m,is_def,ps);
  let x = (try Hashtbl.find g id with Not_found -> (IntSet.empty,None,false,p)) in
  Hashtbl.replace g id x;
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
| Pattern(ps,ol,an::[]) ->
  get_placeholder_value_annot_atom an
| Pattern(ps,ol,anl) -> StringVal(ps,String.make 2 placeholder_char)

and get_placeholder_value_annot_atom (an : annot_atom_t) : value_t = match an with
| SingletonAnnotAtom(ps,a,o) -> get_placeholder_value_atom a
| QuantAnnotAtom(ps,an,q,o) -> StringVal(ps,String.make 2 placeholder_char)

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
  ProdDecl(p,Production(p2,name,[Pattern(p2,([],None),[SingletonAnnotAtom(p2,v,([],None))])]))
| _ -> d

(*******************************************)
(** TYPECHECKING                          **)
(*******************************************)

(*type prod_hashtbl = (symb,production_t * typ_t option) Hashtbl.t

let typecast (old_type : typ_t) (new_type : typ_t) : code = EmptyCode(NoPos) (* TODO XXX *)

let rec get_type (a : annot_atom_t) (prod_table : prod_hashtbl) : (typ_t*code option) =
match a with
| SingletonAnnotAtom(p,EmptyAtom(p2)) -> (SimpleType(p2,NoType(p2)),None)
| SingletonAnnotAtom(p,EofAtom(p2)) -> (SimpleType(p2,NoType(p2)),None)
| SingletonAnnotAtom(p,StringAtom(p2,s)) -> (SimpleType(p2,IdentType(p2,[string_kw])),None)
| SingletonAnnotAtom(p,IdentAtom(p2,name)) ->
  let typo = (try let (_,x) = Hashtbl.find prod_table name in x with Not_found -> None) in
  ((match typo with None -> SimpleType(p2,AnyType(p2)) | Some(t) -> t),None) (* TODO XXX *)
| SingletonAnnotAtom(p,CharsetAtom(p2,cs,cso)) -> (SimpleType(p2,IdentType(p2,[string_kw])),None)
| SingletonAnnotAtom(p,RecurAtom(p2,s1,s2)) -> (SimpleType(p2,IdentType(p2,[string_kw])),None)
| SingletonAnnotAtom(p,ProdAtom(p2,_)) -> die_error p2 "production not flattened properly"
| QuantAnnotAtom(p,a,StarQuant(p2)) ->
  let (old_type,old_code) = get_type a prod_table in
  (CompoundType(p,CommaType(p,[[InstConstrType(p,SingletonConstrType(p,old_type),[list_kw])]])),old_code)
| QuantAnnotAtom(p,a,PlusQuant(p2)) ->
  let (old_type,old_code) = get_type a prod_table in
  let x = SingletonConstrType(p,old_type) in
  (CompoundType(p,CommaType(p,[[x;InstConstrType(p,x,[list_kw])]])),old_code)
| QuantAnnotAtom(p,a,QuestionQuant(p2)) ->
  let (old_type,old_code) = get_type a prod_table in
  (CompoundType(p,CommaType(p,[[InstConstrType(p,SingletonConstrType(p,old_type),[option_kw])]])),None)
| OptAnnotAtom(p,a,TypeOption(p2,t)) -> let (old_type,old_code) = get_type a prod_table in (t,old_code) (* TODO XXX - do the cast here? *)
| OptAnnotAtom(p,a,CodeOption(p2,so,c)) -> let (old_type,old_code) = get_type a prod_table in (old_type,Some(c))
| OptAnnotAtom(p,a,_) -> get_type a prod_table

let typecheck (g : grammar_t) (comps : (symb*pos_t) list) (count : int) : unit = match g with
| Grammar(pos,(d,dl)) ->
  let prod_table = (Hashtbl.create count : prod_hashtbl) in
  (* set up a map containing all productions *)
  List.iter (fun d ->
    match d with
    (* NOTE - all productions should be named at this point *)
    | ProdDecl(p,(Production(p2,(rto,(Some(name),ol)),pl) as prod)) ->
      Hashtbl.replace prod_table name (prod,None);
      Printf.printf "processing: %s\n%!" (get_symbol name)
    | _ -> ()
  ) (d::dl);
  List.iter (fun (name,ps) ->
    let ((Production(_,(rt,_),pl) as prod),t) = (try Hashtbl.find prod_table name with Not_found -> die_error ps ("could not find production '"^(get_symbol name)^"'")) in
    let is_lexer = (match rt with (Some(Lexer)) -> true | _ -> false) in
    Printf.printf "processing:\nplaceholder = %s\ntype = %s\n%s\n\n%!"
      (match rt with (Some(Lexer)) -> (str_value_t (get_placeholder_value_production prod)) | _ -> "[not lexer]")
      (str_x_list (fun (Pattern(_,_,al)) -> str_x_list (str_pair str_typ_t (str_option str_code)) (List.map (fun x -> (if (not is_lexer) then get_type x prod_table else (SimpleType(NoPos,NoType(NoPos)),None))) al) ", ") pl "; ") (str_production_t prod)
  ) comps
  (* TODO XXX *)
  *)
