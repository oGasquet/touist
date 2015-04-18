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

(*** MODULES ******************************************************************)
module F = Format;;
module M = Monad;;
module XO = XmlOutput;;

(*** OPENS ********************************************************************)
open Util;;

(*** INCLUDES *****************************************************************)
include Prelude.Context;;

(*** FUNCTIONS ****************************************************************)
let (>>=) = M.(>>=);;

(* Printers *)
let rec fprintfx = function
  | Hole -> XO.leaf "box"
  | More (f, us, c, vs) -> XO.node "funContext" [
    M.fprintfx_fun f;
    XO.node "before" (List.map Term.fprintfx us);
    fprintfx c;
    XO.node "after" (List.map Term.fprintfx vs)]
;;

let to_stringx t =
 fprintfx t F.str_formatter >>= (M.return <.> F.flush_str_formatter)
;;
