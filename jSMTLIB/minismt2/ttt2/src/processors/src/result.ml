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
module P = Problem;;

(*** OPENS ********************************************************************)
open Util;;
open Rewritingx;;

(*** TYPES ********************************************************************)
type subproblem = P.t list;;
type t = Yes of subproblem | No;;

(* Constructors and Destructors *)
let make_yes ps = Yes ps;;
let make_no = No;;
let yes = function Yes ps -> ps | _ -> failwith "yes without content"
let no = function No -> () | _ -> failwith "no without content"

(* Properties *)
let is_yes = function Yes _ -> true | _ -> false
let is_no = function No -> true | _ -> false

(* Utilities *)
let get_ops = function Yes ps -> ps | No -> []

