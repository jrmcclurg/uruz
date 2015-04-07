open Bootstrap_utils

(* flag defaults *)
let only_flatten = ref false

let def_prod_type = ref Parser
let def_prod_name = ref "Production" (* TODO XXX - make this unique? *)
let def_prod_index = ref 0

let file_prefix = ref None
let param_name = ref "x"
let type_name = ref "t"
let lexer_prefix = ref "Lex"
let auto_type_suffix = ref "_t"
let pos_type_name = ref (add_symbol "pos_t")
let enable_pos = ref true
let def_assoc = ref "left"
let start_prod = ref (None : symb option)
let out_dir = ref (None : string option)

let lexer_code = ref (None : (symb option * code) option)
let parser_code = ref (None : (symb option * code) option)
let ast_code = ref (None : (symb option * code) option)
let utils_code = ref (None : (symb option * code) option)

let typecast_table = Hashtbl.create 100
let def_val_table = Hashtbl.create 10

(* prefix functionality *)
let get_filename_dir filename = 
  let dirname = Filename.dirname filename in
  let result  = (dirname^Filename.dir_sep) in
  result

let get_filename filename = 
  let basename = Filename.basename filename in
  let name     = Filename.chop_extension basename in
  name

let get_filename_prefix filename = 
  ((get_filename filename)^"_")

let get_prefix () = match (!filename,!file_prefix) with
  | (_,Some(pr)) -> pr
  | (f,_) -> (get_filename f)^"_"

let init_tables () =
(* default values *)
Hashtbl.replace def_val_table string_kw "\"\"";
Hashtbl.replace def_val_table int_kw "0";
Hashtbl.replace def_val_table bool_kw "false";
Hashtbl.replace def_val_table float_kw "0.0";
Hashtbl.replace def_val_table char_kw "' '";
Hashtbl.replace def_val_table int32_kw "0l";
Hashtbl.replace def_val_table int64_kw "0L";
(* string -> x *)
Hashtbl.replace typecast_table (string_kw,bool_kw) "bool_of_string";
Hashtbl.replace typecast_table (bool_kw,string_kw) "string_of_bool";
Hashtbl.replace typecast_table (string_kw,int_kw) "int_of_string";
Hashtbl.replace typecast_table (int_kw,string_kw) "string_of_int";
Hashtbl.replace typecast_table (string_kw,char_kw) "(fun s -> String.get s 0)";
Hashtbl.replace typecast_table (char_kw,string_kw) "(String.make 1)";
Hashtbl.replace typecast_table (string_kw,float_kw) "float_of_string";
Hashtbl.replace typecast_table (float_kw,string_kw) "string_of_float";
Hashtbl.replace typecast_table (string_kw,int64_kw) "Int64.of_string";
Hashtbl.replace typecast_table (int64_kw,string_kw) "Int64.to_string";
Hashtbl.replace typecast_table (string_kw,int32_kw) "Int32.of_string";
Hashtbl.replace typecast_table (int32_kw,string_kw) "Int32.to_string";
(* int -> x *)
Hashtbl.replace typecast_table (int_kw,char_kw) "char_of_int";
Hashtbl.replace typecast_table (char_kw,int_kw) "int_of_char";
Hashtbl.replace typecast_table (int_kw,bool_kw) "(fun i -> i > 0)";
Hashtbl.replace typecast_table (bool_kw,int_kw) "(fun b -> if b then 1 else 0)";
Hashtbl.replace typecast_table (int_kw,float_kw) "float_of_int";
Hashtbl.replace typecast_table (float_kw,int_kw) "int_of_float";
Hashtbl.replace typecast_table (int_kw,int64_kw) "Int64.of_int";
Hashtbl.replace typecast_table (int64_kw,int_kw) "Int64.to_int";
Hashtbl.replace typecast_table (int_kw,int32_kw) "Int32.of_int";
Hashtbl.replace typecast_table (int32_kw,int_kw) "Int32.to_int";
(* bool -> x *)
Hashtbl.replace typecast_table (bool_kw,char_kw) "(fun b -> if b then 't' else 'f')";
Hashtbl.replace typecast_table (char_kw,bool_kw) "(fun x -> match Char.lowercase x with 'f' | '0' -> false | _ -> true)";
Hashtbl.replace typecast_table (bool_kw,float_kw) "(fun b -> if b then 1.0 else 0.0)";
Hashtbl.replace typecast_table (float_kw,bool_kw) "(fun i -> i > 0.0)";
Hashtbl.replace typecast_table (bool_kw,int32_kw) "(fun b -> if b then 1l else 0l)";
Hashtbl.replace typecast_table (int32_kw,bool_kw) "(fun i -> (compare i 0l) > 0)";
Hashtbl.replace typecast_table (bool_kw,int64_kw) "(fun b -> if b then 1L else 0L)";
Hashtbl.replace typecast_table (int64_kw,bool_kw) "(fun i -> (compare i 0L) > 0)";
(* float -> x *)
Hashtbl.replace typecast_table (float_kw,char_kw) "(fun x -> char_of_int (int_of_float x))";
Hashtbl.replace typecast_table (char_kw,float_kw) "(fun x -> float_of_int (int_of_char x))";
Hashtbl.replace typecast_table (float_kw,int64_kw) "Int64.of_float";
Hashtbl.replace typecast_table (float_kw,int64_kw) "Int64.of_float";
Hashtbl.replace typecast_table (float_kw,int32_kw) "Int32.of_float";
Hashtbl.replace typecast_table (float_kw,int32_kw) "Int32.of_float";
(* char -> x *)
Hashtbl.replace typecast_table (char_kw,int64_kw) "(fun x -> Int64.of_int (int_of_char x))";
Hashtbl.replace typecast_table (int64_kw,char_kw) "(fun x -> char_of_int (Int64.to_int x))";
Hashtbl.replace typecast_table (char_kw,int32_kw) "(fun x -> Int32.of_int (int_of_char x))";
Hashtbl.replace typecast_table (int32_kw,char_kw) "(fun x -> char_of_int (Int32.to_int x))";
(* int64 -> x *)
Hashtbl.replace typecast_table (int64_kw,int32_kw) "Int64.to_int32";
Hashtbl.replace typecast_table (int32_kw,int64_kw) "Int64.of_int32"

let get_def_prod_name (name : symb option) (nesting : int list) =
  add_symbol ((match name with None -> !def_prod_name | Some(s) -> get_symbol s)^(List.fold_left (fun str n -> "_"^(string_of_int n)^str) "" nesting))
let get_def_prod_type (t : rule_type option) = match t with None -> !def_prod_type | Some(s) -> s
let is_processing_lexer (deftyp : rule_type option) = (deftyp=Some(Lexer)) || (deftyp=None && !def_prod_type=Lexer)
let is_processing_parser (deftyp : rule_type option) = (deftyp=Some(Parser)) || (deftyp=None && !def_prod_type=Parser)
let is_processing_ast (deftyp : rule_type option) = (deftyp=Some(Ast)) || (deftyp=None && !def_prod_type=Ast)

let banner_text = "Welcome to bootstrap v. 2.0";;
let usage_msg = banner_text^"\n"^
                "Usage: bootstrap [options] <file>";;

(* parse the command-line arguments *)
let args = Arg.align [
   ("-d",        Arg.String(fun x -> out_dir := Some(x)),
                    "<dir> Location for the result files");

   ("-flatten",        Arg.Unit(fun () -> only_flatten := true),
                    " Only flatten the grammar and exit");
];;

let error_usage_msg () =
   Arg.usage args usage_msg;
   exit 1
;;

(* dies with a system error s *)
let die_system_error (s : string) =
   output_string stderr s;
   output_string stderr "\n";
   exit 1
;;

let parse_command_line () : (string option*string) list =
   let fs = ref ([] : (string option*string) list) in
   Arg.parse args (fun x -> fs := (!out_dir,x)::(!fs)) banner_text;
   (* use the command-line filename if one exists, otherwise use stdin *)
   match (List.rev !fs) with
   | [] -> error_usage_msg ()
   | l -> l
;;
