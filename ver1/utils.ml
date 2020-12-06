open Lexing;;
open Parsing;;
open Flags;;

(* data type for file positions *)
type pos = NoPos | Pos of string*int*int;; (* file,line,col *)

exception Parse_error;;
exception Lexing_error;;

(* do_error p s
 *
 * Print error message
 *
 * p - the location of the error
 * s - the error message
 *
 * returns unit
 *)
let do_error (p : pos) (s : string) : unit =
   print_string "Error";
   print_string (match p with
   | NoPos -> ""
   | Pos(file_name,line_num,col_num) -> (" in '"^file_name^
    "' on line "^(string_of_int line_num)^" col "^(string_of_int
    col_num))
   );
   print_string (": "^s^"\n")
;;

let die_error (p : pos) (s : string) =
   do_error p s;
   exit 1;
;;

(* dies with a general position-based error *)
let pos_error (s : string) (p : position) = 
   let file_name = p.Lexing.pos_fname in
   let line_num  = p.Lexing.pos_lnum  in
   let col_num   = (p.Lexing.pos_cnum-p.Lexing.pos_bol+1) in
   let ps        = Pos(file_name,line_num,col_num) in
   do_error ps s
;;

(* dies with a parse error s *)
let parse_error (s : string) = 
   pos_error s (symbol_end_pos ());
   raise Parse_error
;;

(* dies with a lexing error *)
let lex_error (s : string) (lexbuf : Lexing.lexbuf) = 
   pos_error s (Lexing.lexeme_end_p lexbuf);
   raise Lexing_error
;;

(* gets a pos data structure using the current lexing pos *)
let get_current_pos () =
   let p         = symbol_start_pos () in
   let file_name = p.Lexing.pos_fname  in
   let line_num  = p.Lexing.pos_lnum   in
   let col_num   = (p.Lexing.pos_cnum-p.Lexing.pos_bol+1) in
   Pos(file_name,line_num,col_num)
;;

(* gets a pos data structure from a lexing position *)
let get_pos (p : Lexing.position) =
   let file_name = p.Lexing.pos_fname in
   let line_num  = p.Lexing.pos_lnum  in
   let col_num   = (p.Lexing.pos_cnum-p.Lexing.pos_bol+1) in
   Pos(file_name,line_num,col_num)
;;

(* updates the lexer position to the next line
 * (this is used since we skip newlines in the
 *  lexer, but we still wish to remember them
 *  for proper line positions) *)
let do_newline lb = 
   Lexing.new_line lb
;;

(* dies with a system error s *)
let die_system_error (s : string) =
   print_string s;
   print_string "\n";
   exit 1
;;

let rec count_newlines s lb = match s with
  | "" -> 0
  | _  -> let c = String.sub s 0 1 in
          let cs = String.sub s 1 ((String.length s)-1) in
          if (c="\n") then (do_newline lb; 1+(count_newlines cs lb))
                      else (count_newlines cs lb)
;;

let is_capitalized (s : string) : bool =
  ((String.capitalize_ascii s) = s)
;;

let rec to_type_case (s : string) : string =
   to_case_helper s false false

and to_token_case (s : string) : string =
   to_case_helper s false true

and to_case_helper (s : string) (prev_lower : bool) (upper : bool) : string =
   let len = String.length s in
   if len <= 0 then s
   else (
      let c = String.sub s 0 1 in
      let rest = String.sub s 1 (len-1) in
      let c2 = String.lowercase_ascii c in
      let this_lower = (c2 = c) in
      ((if (prev_lower && (not this_lower)) then "_" else "")^
      (if upper then (String.uppercase_ascii c) else c2)^
      (to_case_helper rest this_lower upper))
   )
;;

let str_starts_with (s : string) (prefix : string) : (bool * string) =
   let len = String.length s in
   let p_len = String.length prefix in
   if len < p_len then (false,s)
   else ((String.sub s 0 p_len) = prefix, String.sub s p_len (len-p_len))
;;

let str_remove_from_front (s : string) (prefix : string) : string =
   (*let (t,rest) = str_starts_with s prefix in
   let result = (if t then rest else s) in
   result*)
   s
;;

let parse_command_line () : in_channel =
   let f_set = ref false in
   Arg.parse args (fun x -> f_set := true; filename := x) banner_text;
   (* use the command-line filename if one exists, otherwise use stdin *)
   match !f_set with
   | false -> error_usage_msg ()
   | true -> (
      try (open_in !filename)
      with _ -> die_system_error ("can't read from file: "^(!filename))
   )
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

let rec string_explode (s:string) : char list =
   if (String.length s) > 0 then
      (String.get s 0)::(string_explode (String.sub s 1 ((String.length s)-1)))
   else
      []
;;

let rec string_combine (cl : char list) : string =
   match cl with
   | [] -> ""
   | c::more -> (String.make 1 c)^(string_combine more)

let three_hd (cl: char list) : char list * char list = 
   match cl with
   | a::b::c::l -> (a::b::c::[],l)
   | a::b::l    -> (a::b::[],l)
   | a::l       -> (a::[],l)
   | _          -> ([],cl)
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

let is_string_empty (s : string) : bool =
   (*print_string ("is_empty("^s^")=");*)
   let sp = "[\r\n\t ]+" in
   let t = Str.global_replace (Str.regexp sp) "" s in
   let result = (if t = "" then true else false) in
   (*print_string (if result then "yes" else "no");
   print_string "\n";*)
   result
;;

(* list comprehension *)
let rec list_comp (start : int) (fin : int) : int list =
   if (start > fin) then []
   else if (start = fin) then [start]
   else (start::(list_comp (start+1) fin))
;;

let rec str_list (f : 'a -> string) (l : 'a list) : string =
   str_list_helper f l true

and str_list_helper (f : 'a -> string) (l : 'a list) (first : bool) : string =
   match l with
   | [] -> ""
   | a::more -> ((if (not first) then " " else "")^(f a)^(str_list_helper f more false))
;;

(* strips (recursive) OCaml comments from a string *)
let rec strip_ocaml_comments (s : string) : string =
   string_combine (strip_ocaml_comments_helper (string_explode s) [] 0)
   
and strip_ocaml_comments_helper (cl : char list) (unknown : char list) (level : int) : char list =
   match cl with
   | c1::c2::more ->
      if ((c1 = '(') && (c2 = '*')) then strip_ocaml_comments_helper more (unknown @ [c1;c2]) (level+1)
      else if ((c1 = '*') && (c2 = ')')) then strip_ocaml_comments_helper more (if (level=1) then [] else unknown@[c1;c2]) (level-1)
      else if (level > 0) then strip_ocaml_comments_helper (c2::more) (unknown@[c1]) level
      else c1::(strip_ocaml_comments_helper (c2::more) unknown level)
   | [c] -> c::unknown
   | [] -> unknown
;;

(*let rec strip_outer_parens (s : string) : string =
   string_combine (strip_outer_parens_helper (string_explode s) 0)*)

let rec char_list_contains (cl : char list) (c : char) : bool =
   match cl with
   | [] -> false
   | ct::more -> if (ct=c) then true else char_list_contains more c
;;

let rec get_intersect_char (cl1 : char list) (cl2 : char list) : char option =
   match cl1 with
   | [] -> None
   | c::more -> if (char_list_contains cl2 c) then Some(c) else get_intersect_char more cl2
;;

let rec get_diff_char (cl1 : char list) (cl2 : char list) : char option =
   match cl1 with
   | [] -> None
   | c::more -> if (not (char_list_contains cl2 c)) then Some(c) else get_diff_char more cl2
;;

let rec get_bounds_char_helper (cl : char list) (min : char) (max : char) : (char * char) =
   match cl with
   | [] -> (min,max)
   | c::more -> get_bounds_char_helper more (if (c < min) then c else min) (if (c > max) then c else max)
;;

let get_bounds_char (cl : char list) : (char * char) =
   get_bounds_char_helper cl (Char.chr 255) (Char.chr 0)
;;

(* NOTE - min <= max must be the case! *)
let rec get_chars (min : char) (max : char) : char list =
   if (min > max) then []
   else if (min = max) then [min]
   else min::(get_chars (Char.chr ((Char.code min)+1)) max)
;;

let rec get_unused_char (cl : char list) : char option =
   let (min,max) = get_bounds_char cl in
   let temp = get_chars min max in
   let c = get_diff_char temp cl in
   match (c,min,max) with
   | (None,'\x00','\xFF') -> None
   | (None,'\x00',_) -> Some(Char.chr ((Char.code max)+1)) 
   | (None,_,'\xFF') -> Some(Char.chr ((Char.code min)-1)) 
   | (None,_,_) -> Some(Char.chr ((Char.code min)-1)) 
   | (Some(_),_,_) -> c
;;

let charop_to_strop (co : char option) : string option =
   match co with
   | None -> None
   | Some(c) -> Some(String.make 1 c)
;;

let get_first_strop (cl : char list) : string option =
   match cl with
   | [] -> None
   | c::more -> Some(String.make 1 c)
;;
