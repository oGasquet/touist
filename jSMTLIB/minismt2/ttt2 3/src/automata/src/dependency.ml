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

(*** MODULES ******************************************************************)
module S = State;;

module States = struct
 type t = State.t list;;

 let normalize = List.sort S.compare;;

 let compare ps = compare (normalize ps) <.> normalize;;
 let copy = id;;
 let fprintf = List.fprintf S.fprintf ",";;
 let hash = Hashtbl.hash <.> normalize;;
end

(*** INCLUDES *****************************************************************)
include Isomorphism.Make (State) (States);;

(* The Isomorphism / Hashtbl modules use Pervasives.compare so we better do
 * our own normalisation *)
let add d r = add d (States.normalize r);;
let replace d r = replace d (States.normalize r);;
let mem_ran r = mem_ran (States.normalize r);;
let find_dom r = find_dom (States.normalize r);;
