(* Copyright 2012 Bertram Felgenhauer, Martin Korp, Christian Sternagel, Harald Zankl
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
module XO = XmlOutput;;
module F = Format;;
module M = Monad;;

(*** OPENS ********************************************************************)
open Util;;

(*** FUNCTIONS ****************************************************************)
let (>>=) = M.(>>=);;

let get_rp s trs t = 
 let prs = List.product (Trs.to_list trs) (Term.pos s) in
 List.find (fun (r,p) -> Rule.rewrites s p r t) prs
;;

let reconstruct_steps (strict, weak) ts =
  let trs = Trs.union strict weak in
  let rec seq acc = function
    | [_] -> List.rev acc
    | t::(u::_ as ts) ->
      let (r, p) = get_rp t trs u in
      seq ((p, r, Trs.mem r weak, u)::acc) ts
    | _ -> failwith "Sequence.reconstruct_steps: empty list"
  in
    seq [] ts
;;

let fprintfx_step (p, r, rel, t) = XO.node "rewriteStep" [
  Position.fprintfx p;
  Rule.fprintfx r;
  if rel then XO.leaf "relative" else XO.id;
  Term.fprintfx t
];;

let fprintfx trs (startterm :: _ as seq) =
    XO.node "rewriteSequence" (
      XO.node "startTerm" [Term.fprintfx startterm]
      :: List.map fprintfx_step (reconstruct_steps trs seq)
    )
;;
