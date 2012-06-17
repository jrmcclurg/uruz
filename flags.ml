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
let default_prefix = "pgg_";;

(* flag defaults *)
let filename = ref (None : string option);;
let verbose_mode = ref false;;
let out_dir = ref ".";;
let file_prefix = ref (None : string option);;

(* banner functionality *)
let rec get_version_string (s : string) (k : int) : string =
   let len = String.length s in
   if len <= k then s
   else ((String.sub s 0 1)^"."^(get_version_string (String.sub s 1 (len-1)) k))
;;

let version = ("1."^(get_version_string commit_num 1));;
let banner_text = "Parser Generator Generator v. "^version^" by Jedidiah McClurg\n"^
                  "(build date "^build_date^")"^
                  "";;

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
                    " Emit the generated assembly code");
   ("-target",   Arg.Int(fun x -> target_lang := x),
                    "<k> Set the target language to Lk (default to n-1)");*)
   ("-o",        Arg.String(fun x -> out_dir := x),
                    "<dir> Location of the result files (default \".\")");
   ("-prefix",   Arg.String(fun x -> file_prefix := Some(x)),
                    "<string> Prefix for the filenames (default \""^default_prefix^"\")");
];;
