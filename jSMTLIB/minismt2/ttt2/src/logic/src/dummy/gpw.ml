(* Dummy module for builds without Gpw support *)

(*** FUNCTIONS ****************************************************************)
let fail _ =
  Format.printf
    "You used a processor that relies on Gpw internally.\n\
    However, Gpw is not supported by this build of TTT2.\n";
  exit 1
;;

let solve f = fail ()
let eval_a a ass = fail ()
let eval_p p ass = fail ()
