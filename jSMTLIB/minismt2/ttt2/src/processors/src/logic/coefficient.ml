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
open Logic.Operators;;

(*** FUNCTIONS ****************************************************************)
 type t = Logic.a;;
 let add = (<+>);;
 let mul = (<*>);;
 let scale = Logic.scale;;
 let zero = Logic.zero;;
 let one = Logic.one;;
 let is_zero a = a = Logic.zero;; (*test for syntactic equality*)
 let is_one a = a = Logic.one;; (*test for syntacitc equality*)
 let fprintf = Logic.fprintf_a;;
 let fprintfx ppf = failwith "Coefficient.fprintx: not supported";;
 let to_string a = 
  Format.fprintf Format.str_formatter "%a" fprintf a;
  Format.flush_str_formatter ();;
 let gt = (<>>);;
 let eq = (<=>);;
 let geq = (<>=>);;
 let of_int = Logic.Number.of_int;;
 let big_sum = Logic.big_sum;;
