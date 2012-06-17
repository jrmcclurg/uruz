open Lexing;;
open Parsing;;
open Flags;;

(* data type for file positions *)
type pos = NoPos | Pos of string*int*int;; (* file,line,col *)

exception Parse_error;;

(* dies with a system error s *)
let die_system_error (s : string) =
   print_string s;
   print_string "\n";
   exit 1
;;

let parse_error s = 
  let p         = symbol_end_pos ()  in
  let file_name = p.Lexing.pos_fname in
  let line_num  = p.Lexing.pos_lnum  in
  let col_num   = (p.Lexing.pos_cnum-p.Lexing.pos_bol+1) in
  print_string ("Parse error in '"^file_name^
    "' on line "^(string_of_int line_num)^" col "^(string_of_int
    col_num)^"!\n"
  );
  exit (-1)
;;

let get_current_pos () =
  let p         = symbol_start_pos () in
  let file_name = p.Lexing.pos_fname  in
  let line_num  = p.Lexing.pos_lnum   in
  let col_num   = (p.Lexing.pos_cnum-p.Lexing.pos_bol+1) in
  Pos(file_name,line_num,col_num)
;;

let get_pos p =
  let file_name = p.Lexing.pos_fname in
  let line_num  = p.Lexing.pos_lnum  in
  let col_num   = (p.Lexing.pos_cnum-p.Lexing.pos_bol+1) in
  Pos(file_name,line_num,col_num)
;;

exception Lexing_error;;

let do_newline lb = 
  Lexing.new_line lb
;;

let rec count_newlines s lb = match s with
  | "" -> 0
  | _  -> let c = String.sub s 0 1 in
          let cs = String.sub s 1 ((String.length s)-1) in
          if (c="\n") then (do_newline lb; 1+(count_newlines cs lb))
                      else (count_newlines cs lb)
;;

let is_capitalized (s : string) : bool =
  ((String.capitalize s) = s)
;;

let parse_command_line () : in_channel =
   Arg.parse args (fun x -> filename := Some(x)) banner_text;
   (* use the command-line filename if one exists, otherwise use stdin *)
   match !filename with
   | None -> stdin
   | Some(fn) -> (
      try (open_in fn)
      with _ -> die_system_error ("can't read from file: "^fn)
   )
;;
