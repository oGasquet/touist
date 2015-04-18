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
module C = Complexity;;
module F = Format;;
module M = Monad;;
module P = Problem;;
module XO = XmlOutput;;

(*** TYPES ********************************************************************)
type flags = {
  help  : bool ref;
  steps : int  ref;
  };;
type t = P.t * P.t;;

(*** GLOBALS ******************************************************************)
let code = "commute";;
let name = "Commute Transformation Processor";;

let comment =
 "Adds symmetric lhs if f(x,y) -> f(y,x) is present."
;;

let keywords = ["commutativity";"transformation"];;
let flags = {
  help  = ref false;
  steps = ref 5;
  };;

let spec =
 let spec = [
  ("--help",Arg.Set flags.help,"Prints information about flags.");
  ("-help",Arg.Set flags.help,"Prints information about flags.");
  ("-h",Arg.Set flags.help,"Prints information about flags.");
  ("-steps",Arg.Set_int flags.steps,
   Format.sprintf "Steps to rewrite [default %d]." !(flags.steps));
 ] in
 Arg.alignx 80 spec
;;

let help = (comment,keywords,List.map Triple.drop_snd spec);;

(*** FUNCTIONS ****************************************************************)
let (>>=) = M.(>>=);;
let (>>) = M.(>>);;
let init _ = flags.help := false;;

(* Destructors *)
let get_ip = fst;;
let get_op = snd;;

let is_c_rule r = match Rule.to_terms r with
 | (Term.Fun(f,[t0;t1])), (Term.Fun(g,[s0;s1])) ->
   Function.equal f g && Term.equal t0 s1 && Term.equal t1 s0 && 
    Term.is_var t0 && Term.is_var t1
 | _ -> false
;;

let c_rule trs cs rule = match Rule.to_terms rule with
  | (Term.Fun(f,_) as l), (Term.Fun(g,_) as r) when
   (* Function.equal f g && List.mem f cs && *)
    List.mem l (Rewrite.reducts ~n:!(flags.steps) r trs) ->
   [rule;Rule.invert rule]
  | Term.Fun(f,ts),r 
   when List.mem f cs -> 
   [rule;Rule.of_terms (Term.Fun(f,List.rev ts)) r]
  | _ -> [rule]
;;

let commutative p = 
 let trs = P.get_trs p in
 let cs = Trs.left_roots (Trs.filter is_c_rule trs) in
 let trs' = Trs.variant_free (Trs.of_list (Trs.flat_map (c_rule trs cs) trs)) in
 if Trs.is_variant trs trs' then
   None
 else
  let q = P.set_trs trs' p in
  Some (p,q)
;;

(* Processor *)
let solve fs p =
  let configurate s = F.printf "%s@\n%!" s; flags.help := true in
  (try init (); Arg.parsex code spec fs with Arg.Bad s -> configurate s);
  if !(flags.help) then (Arg.usage spec ("Options for "^code^":"); exit 0);
  M.return (
    if P.is_crp p then
     commutative p
    else None
  )
;;

(* Complexity Bounds *)
let complexity c _ = C.mul c C.constant;;

(* Compare Functions *)
let equal p q = P.equal (get_ip p) (get_ip q);;

(* Printers *)
let fprintf fs fmt p =
 F.fprintf fmt "@[<1>%s:@\n" name; P.fprintfm fmt (get_op p) >>= fun _ ->
 F.fprintf fmt "@\n"; List.hd fs fmt >>= fun _ -> M.return (F.fprintf fmt "@]")
;;

let fprintfx fs p = XO.node "commuteTrans" [P.fprintfx (get_op p); List.hd fs];;
