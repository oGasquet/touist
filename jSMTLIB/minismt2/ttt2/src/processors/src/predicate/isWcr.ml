(* Copyright 2008 Martin Korp, Christian Sternagel, Harald Zankl
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

(*** OPENS ********************************************************************)
open Util;;
open Rewritingx;;

(*** MODULES ******************************************************************)
module F = Format;;

(*** TYPES ********************************************************************)
type flags = {
  help  : bool ref;
  steps : int ref;
};;
type t = Problem.t * Problem.t;;
let make p q = true ;;

(*** GLOBALS ******************************************************************)
let code = "wcr";;
let name = "WCR Predicate";;
let comment = "Checks if the given system is weak Church-Rosser.";;
let keywords = ["is wcr";"locally confluent";"predicate"];;
let flags = {
 help = ref false;
 steps = ref ~-1;
};;

let spec =
 let spec = [
  ("--help",Arg.Set flags.help,"Prints information about flags.");
  ("-help",Arg.Set flags.help,"Prints information about flags.");
  ("-h",Arg.Set flags.help,"Prints information about flags.");
  ("-steps",Arg.Set_int flags.steps,"DEPRECATED (more efficient if option not used): Limit length of joining sequences.");
 ] in
 Arg.alignx 80 spec
;;

let help = (comment,keywords,List.map Triple.drop_snd spec);;

(*** FUNCTIONS ****************************************************************)
let (>>=) = Monad.(>>=);;
let (>>) = Monad.(>>);;

let init _ = 
 flags.help := false;
 flags.steps := ~-1; 
;;

let min_join_wcr trs = 
 Monad.liftM Option.is_some (Diagram.critical_diagrams trs )
;;

let solve fs p =
 let configurate s = F.printf "%s@\n%!" s; flags.help := true in
 (try init (); Arg.parsex code spec fs with Arg.Bad s -> configurate s);
 if !(flags.help) then (Arg.usage spec ("Options for "^code^":"); exit 0);
 let n = !(flags.steps) in
 if Problem.is_sp p then
  (if n >= 0 then Rewrite.is_wcr ~n:n (Problem.get_trs p)
  else min_join_wcr (Problem.get_trs p)) >>= fun b ->
  if b then
   Monad.return (make p p)
  else
   Monad.return false
 else 
  Monad.return false
;;
