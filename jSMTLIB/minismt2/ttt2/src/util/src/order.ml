(* Copyright 2013 Bertram Felgenhauer
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
open Prelude;;

(*** TYPES ********************************************************************)
type t = GT | EQ | NONE;;

(*** FUNCTIONS ****************************************************************)
let is_gt = function
 | GT -> true
 | _  -> false
;;

let is_eq = function
 | EQ -> true
 | _ -> false
;;

let is_ge = function
 | GT -> true
 | EQ -> true
 | _  -> false
;;

let rec lex = function
 | [] -> EQ
 | GT :: xs -> GT
 | EQ :: xs -> lex xs
 | _ -> NONE
;;

(* Printers *)
let fprintf fmt = function
 | GT -> Format.fprintf fmt ">"
 | EQ -> Format.fprintf fmt "="
 | NONE -> Format.fprintf fmt "?"
;;

(*let fprintfx fmt = Format.fprintf fmt "@{<number>%i@}";;*)
let to_string = Format.flush_str_formatter <.> fprintf Format.str_formatter;;
