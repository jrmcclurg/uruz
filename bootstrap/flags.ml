open Bootstrap_utils

(* flag defaults *)
let filename = ref "";; (* TODO - this will always be set *)
let out_file = ref (None : string option)

let def_prod_type = ref Parser
let def_prod_name = ref "Production" (* TODO XXX - make this unique? *)
let def_prod_index = ref 0

let get_def_prod_name (name : symb option) (nesting : int list) =
  add_symbol ((match name with None -> !def_prod_name | Some(s) -> get_symbol s)^(List.fold_left (fun str n -> "_"^(string_of_int n)^str) "" nesting))
let get_def_prod_type (t : rule_type option) = match t with None -> !def_prod_type | Some(s) -> s
let is_processing_lexer (deftyp : rule_type option) = (deftyp=Some(Lexer)) || (deftyp=None && !def_prod_type=Lexer)

let banner_text = "Welcome to bootstrap v. 1.0";;
let usage_msg = banner_text^"\n"^
                "Usage: bootstrap [options] <file>";;

(* parse the command-line arguments *)
let args = Arg.align [
   ("-o",        Arg.String(fun x -> out_file := Some(x)),
                    "<file> Location for the result");
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
