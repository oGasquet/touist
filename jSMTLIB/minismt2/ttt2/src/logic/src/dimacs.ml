(* Copyright 2011 Simon Legner, Christian Sternagel, Harald Zankl
 * GNU Lesser General Public License
 *
 * This file is part of TTT2.
 *
 * TTT2 is free software: you can redistribute it and/or modify it under
 * the terms of the GNU Lesser General Public License as published by the
 * Free Software Foundation, either version 3 of the License, or (at your
 * option) any later version.
 *
 * TTT2 is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public
 * License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with TTT2. If not, see <http://www.gnu.org/licenses/>.
 *)

open Util;;
open Parsec;;
include StringParser;;

let comment = char 'c' >> many (noneof "\n") >> spaces;;

let nat =
  oneof "123456789" >>= fun c ->
  many digit >>= fun cs ->
  spaces >>
  return (String.of_char_list (c::cs))
;;

let header =
  char 'p' >>
  spaces >>
  string "cnf" >>
  spaces >>
  nat >>= fun v ->
  nat >>= fun c ->
  return (v, c)
;;

let var =
  option true (char '-' >> return false) >>= fun b ->
  nat >>= fun x ->
  spaces >>
  return (x, b)
;;

let clause =
  many var >>= fun xs ->
  char '0' >>
  spaces >>
  return xs
;;

let dimacs =
  spaces >>
  many comment >>
  header >>= fun (v, c) ->
  many clause >>= fun cs ->
  eoi >>
  return (v, c, cs)
;;

(* auxiliary printers *)
let pvar fmt (x, b) = Format.fprintf fmt "(%s,%b)" x b;;
let pclause fmt vs = List.fprintf pvar ",@ " fmt vs;;
let pclauses fmt cs = List.fprintf pclause "@\n" fmt cs;;

let main () =
  let toks = StringInput.of_file Sys.argv.(1) in
  match parse dimacs toks with
    Left e -> (Printf.eprintf "%s\n" (Error.to_string e); exit 1)
  | Right (v, c, cs) ->
    Format.fprintf Format.std_formatter "maximal variable index: %s@\n\
      number of clauses: %s@\n\
      clauses:@\n%a%!" v c pclauses cs
(*
in
  main ();
*)
;;
