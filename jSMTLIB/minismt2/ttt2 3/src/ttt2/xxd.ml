(* OCaml rewrite of Vim's xxd to convert any file in a C header file containing
 * its hex values.
 * In contrast to Vim's xxd, a null terminated array is produced to allow the
 * usage of strlen. When using the _len variable, one encounters no difference.
 *)

#load "str.cma";;

let input_chars_output_hex () =
  let i = ref 0 in
  try
    while true do
      let c = int_of_char (input_char stdin) in
      Format.printf "0x%02x,@ " c;
      i := !i + 1
    done;
    !i
  with End_of_file -> !i
;;

let _ =
  let escape_str = Str.global_replace (Str.regexp_string ".") "_" in
  let filename = escape_str (Sys.argv.(1)) in
  Format.printf "@[<2>unsigned char %s[] = {@\n" filename;
  let len = input_chars_output_hex () in
  Format.printf "0x00@]@\n};@\n";
  Format.printf "unsigned int %s_len = %d;@." filename len
;;

