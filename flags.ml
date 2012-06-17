(*
 * Parser Generator Generator
 * Jedidiah R. McClurg
 * Northwestern University
 *
 * flags.ml
 * Utilities for the command-line arguments
 *)
open Version;;

let get_revision () = commit_num ;;

(* flag defaults *)
let banner_text = "Parser Generator Generator v. 1.0\nby Jedidiah McClurg";;
let filename = ref (None : string option);;
let verbose_mode = ref false;;
let out_file_name = ref (None : string option);;

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
   ("-o",        Arg.String(fun x -> out_file_name := Some(x)),
                    "<file> Location of the result");
];;
