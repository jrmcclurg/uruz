(*
 * Parser Generator Generator
 * Jedidiah R. McClurg
 * Northwestern University
 *
 * flags.ml
 * Utilities for the command-line arguments
 *)
open Version;;

(* constants *)

(* flag defaults *)
type compiler_type = OCamlC | OCamlOpt | OCamlCp;;

let filename = ref "";; (* TODO - this will always be set *)
let verbose_mode = ref false;;
let out_dir = ref ".";;
let out_file = ref (None : string option);;
let file_prefix = ref (None : string option);;
let gen_skeleton = ref true;;
let compiler = ref OCamlOpt;;
let opt_level = ref (None : string option);;
let compile_static = ref false;;
let debug_symbols = ref false;;
let libs = (Hashtbl.create 5 : (string,unit) Hashtbl.t);;

let error_and_exit s =
   output_string stderr ("Error: "^s^"\n");
   exit 1
;;

(* prefix functionality *)
let get_filename_dir filename = 
  let dirname = Filename.dirname filename in
  let result  = (dirname^Filename.dir_sep) in
  result
;;

let get_filename filename = 
  let basename = Filename.basename filename in
  let name     = Filename.chop_extension basename in
  name
;;

let get_filename_prefix filename = 
  ((get_filename filename)^"_")
;;

let get_prefix () = match (!filename,!file_prefix) with
  | (_,Some(pr)) -> pr
  | (f,_) -> (get_filename f)^"_"
;;

let get_out_file () = match (!filename,!out_file) with
  | (_,Some(s)) -> s
  | (f,_) -> (get_filename f)
;;

(* banner functionality *)
let rec pad_string (s : string) (n : int) : string =
   let len = String.length s in
   if (len >= n) then s
   else (pad_string ("0"^s) n)
;;

let rec get_version_string (s : string) (k : int) : string =
   let len = String.length s in
   if len <= k then s
   else ((String.sub s 0 1)^"."^(get_version_string (String.sub s 1 (len-1)) k))
;;

let version = ("1."^(get_version_string (pad_string commit_num 3) 1));;
let banner_text = "Parser Generator Generator v. "^version^"\n"^
                  "by Jedidiah McClurg, www.jrmcclurg.com\n"^
                  "(build date "^build_date^")"^
                  "";;
let usage_msg = banner_text^"\n"^
                "Usage: pgg [options] <grammar_file>";;

(* parse the command-line arguments *)
let args = Arg.align [
   ("-v",        Arg.Unit(fun x -> verbose_mode := true),
                    " Turn on verbose output");
   ("-verbose",  Arg.Unit(fun x -> verbose_mode := true),
                    " Turn on verbose output");
   (*("-heap",     Arg.Int(fun x -> heap_size := x),
                    "<size> Set the heap size in bytes (default 1048576)");
   ("-nogc",     Arg.Unit(fun x -> gc_enabled := false),
                    " Turn off runtime garbage collection");
   ("-noclear",  Arg.Unit(fun x -> clear_uninit := false),
                    " Turn off clearing of stack/callee-saves (may impede GC performance)");
   ("-runtime",  Arg.Unit(fun x -> emit_runtime := true),
                    " Emit the C runtime");
   ("-asm",      Arg.Unit(fun x -> emit_asm := true),
                    " Emit the generated assembly code"); *)
   ("-O",        Arg.String(fun x -> opt_level := Some(x)),
                    "<k> Set the compiler optimization level to -Ok");
   ("-static",   Arg.Unit(fun x -> compile_static := true),
                    " Force compiler to do static linking");
   ("-no-opt",   Arg.Unit(fun x -> compiler := OCamlC),
                    " Use ocamlc rather than ocamlopt for compilation");
   ("-prof",     Arg.Unit(fun x -> compiler := OCamlCp),
                    " Use ocamlcp rather than ocamlopt for compilation");
   ("-l",        Arg.String(fun x -> Hashtbl.replace libs x ()),
                    "<lib> Link in a library (e.g. \"str\", \"unix\", etc.)");
   ("-no-skel",  Arg.Unit(fun x -> gen_skeleton := false),
                    " Don't create skeleton project files");
   ("-o",        Arg.String(fun x -> out_file := Some(x)),
                    "<file> Location for the compiled binary (default <file-prefix>, "^
                    "or a.out for stdin)");
   ("-d",        Arg.String(fun x -> out_dir := x),
                    "<dir> Location of the result files (default \".\")");
   ("-prefix",   Arg.String(fun x -> file_prefix := Some(x)),
                    "<string> Prefix for the filenames (default <file-prefix>_)");
];;

let error_usage_msg () =
   Arg.usage args usage_msg;
   exit 1
;;
