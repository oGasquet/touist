(*
 * Implementation of the Hello.Main module
 *)
open Util;;
open Rewriting;;
open Monad;;

let run =
  Monad.create_fun 1 "Hello" >>= fun hello ->
  Monad.create_var "World" >>= fun world ->
  let tworld = Term.make_var world in
  let term = Term.make_fun hello [tworld] in
  Term.to_stringm term >>= fun str ->
  Format.printf "%s!\n" str ;
  return ()
;;

let hello _ =
  let sigma = Signature.empty 37 in
  let _ = Monad.run sigma run in
  ()  
;;
