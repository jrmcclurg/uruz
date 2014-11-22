open Bootstrap_ast
open Bootstrap_utils
open Flags

(* HANDLE PROPERTIES *)

let rec handle_props (g : grammar_t) : unit = match g with
| Grammar(pos,code1,(d,dl),code2) ->
  List.iter (fun d -> match d with
    | PropDecl(p,name,value) -> (
      match (name,value) with
      | ("default_production_type",StringVal(p,s)) -> Flags.def_prod_type := s (* TODO XXX - this should only be "parser", "ast", etc. *)
      | ("default_production_name",StringVal(p,s)) -> Flags.def_prod_name := s
      | _ -> die_error p "invalid property name or type"
      )
    | _ -> ()
  ) (d::dl)

(* FLATTEN *)

let rev_flatten (l : 'a list list) : 'a list =
  List.fold_left (fun acc l2 ->
    List.rev_append l2 acc
  ) [] l

let tail_flatten (l : 'a list list) : 'a list =
  List.rev (rev_flatten l)

let flatten_list f l defname deftyp nesting =
let (l2,prods,_) = List.fold_left (fun (l2,prods,index) x ->
  let (x2,prods2) = f x defname deftyp (index::nesting) in
  ((x2::l2), List.rev_append prods2 prods, index+1)
) ([],[], !Flags.def_prod_index) l in
(List.rev l2, List.rev prods)

let rec flatten_grammar (g : grammar_t) : grammar_t = match g with
| Grammar(pos,code1,(d,dl),code2) ->
  (*let dl2 = List.rev_map (fun d -> let (x,y) = flatten_decl d in List.rev (x::y)) (d::dl) in
  let l = rev_flatten dl2 in*)
  let (dl2,_) = List.fold_left (fun (acc,index) d -> let (x,y) = flatten_decl d None None [index] in (List.rev_append (x::y) acc, index+1)) ([],!Flags.def_prod_index) (d::dl) in
  let l = List.rev dl2 in
  Grammar(pos,code1,(List.hd l,List.tl l),code2)

and flatten_decl (d : decl_t) (defname : string option) (deftyp : string option) (nesting : int list) : (decl_t*decl_t list) = match d with
| ProdDecl(p,prod) ->
  let (prod2,dl) = flatten_production prod defname deftyp nesting in
  (ProdDecl(p,prod2),dl)
| _ -> (d,[])

and flatten_production (p : production_t) (defname : string option) (deftyp : string option) (nesting : int list) : (production_t*decl_t list) = match p with
| Production(ps,o,pat,patl) ->
  let (defname,deftyp,nesting) = (match o with
    | Some(kwo,(name,ol)) -> (Some(name),kwo,[])
    | _ -> (defname,deftyp,nesting)
  ) in
  let o2 = (match o with
  | None -> Some(Some(get_def_prod_type deftyp),(get_def_prod_name defname nesting,[]))
  | Some(None,x) -> Some(Some(get_def_prod_type deftyp),x)
  | _ -> o
  ) in
  let (patl2,prods) = flatten_list flatten_pattern (pat::patl) defname deftyp nesting in
  (Production(ps,o2,List.hd patl2,List.tl patl2),prods)

and flatten_pattern (p : pattern_t) (defname : string option) (deftyp : string option) (nesting : int list) : (pattern_t*decl_t list) = match p with
| Pattern(p,(a,al),eof) ->
  let (al2,prods) = flatten_list flatten_annot_atom (a::al) defname deftyp nesting in
  (Pattern(p,(List.hd al2,List.tl al2),eof),prods)

and flatten_annot_atom (an : annot_atom_t) (defname : string option) (deftyp : string option) (nesting : int list) : (annot_atom_t*decl_t list) = match an with
| SingletonAnnotAtom(p,a) -> let (a2,prods) = flatten_atom a defname deftyp nesting in (SingletonAnnotAtom(p,a2),prods)
| QuantAnnotAtom(p,an,q) -> let (a2,prods) = flatten_annot_atom an defname deftyp nesting in (QuantAnnotAtom(p,a2,q),prods)
| OptAnnotAtom(p,an,o) -> let (a2,prods) = flatten_annot_atom an defname deftyp nesting in (OptAnnotAtom(p,a2,o),prods)

and flatten_atom (a : atom_t) (defname : string option) (deftyp : string option) (nesting : int list) : (atom_t*decl_t list) = match a with
| ProdAtom(p,Production(p2,None,pat,patl)) ->
  let name = Flags.get_def_prod_name defname nesting in
  let (patl2,prods) = flatten_list flatten_pattern (pat::patl) defname deftyp nesting in
  Printf.printf "flatten_atom\n";
  (IdentAtom(p,name),(ProdDecl(p2,Production(p2,Some(Some(Flags.get_def_prod_type deftyp),(name,[])),List.hd patl2,List.tl patl2)))::prods)
| ProdAtom(p,Production(p2,Some(kwo,(name,ol)),pat,patl)) -> 
  let (patl2,prods) = flatten_list flatten_pattern (pat::patl) (Some(name)) kwo [] in
  Printf.printf "flatten_atom2\n";
  (IdentAtom(p,name),(ProdDecl(p2,Production(p2,Some((match kwo with None -> Some(Flags.get_def_prod_type deftyp) | _ -> kwo),(name,ol)),List.hd patl2,List.tl patl2)))::prods)
| _ -> (a,[])
