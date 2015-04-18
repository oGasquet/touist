(* Dummy module for builds without Yices support *)

(*** FUNCTIONS ****************************************************************)
let fail _ =
  Format.printf
    "You used a processor that relies on Yices internally.\n\
    However, Yices is not supported by this build of TTT2.\n";
  exit 1
;;

let solve f = fail ()
let eval_a a ass = fail ()
let eval_p p ass = fail ()
