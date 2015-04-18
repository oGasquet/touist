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
 help : bool ref;
 copy : bool ref;
 force : bool ref;
 inv : bool ref;
};;
type t = P.t * P.t;;

(*** GLOBALS ******************************************************************)
let code = "rt";;
let name = "RT Transformation Processor";;
let keywords = ["relative termination transformation";"transformation"];;
let flags = {
 help  = ref false;
 copy  = ref false;
 force = ref false;
 inv   = ref false;
};;

let comment =
 "Transforms a given standard termination problem into a relative termination \
 problem."
;;

let spec =
 let spec = [
  ("--help",Arg.Set flags.help,"Prints information about flags.");
  ("-help",Arg.Set flags.help,"Prints information about flags.");
  ("-h",Arg.Set flags.help,"Prints information about flags.");
  ("-copy",Arg.Set flags.copy, "Initializes the strict and weak part of the \
   relative termination problem with the given TRS.");
  ("-force",Arg.Set flags.force,"Ignores check of -inv (unsound for nontermination).");
  ("-inv",Arg.Set flags.inv,"Transform relative problem into standard problem if \
   relative rules are empty.");
 ] in
 Arg.alignx 80 spec
;;

let help = (comment,keywords,List.map Triple.drop_snd spec);;

(*** FUNCTIONS ****************************************************************)
let (>>=) = M.(>>=);;
let init _ = 
 flags.help  := false;
 flags.copy  := false;
 flags.force := false;
 flags.inv   := false;
;;

(* Destructors *)
let get_ip = fst;;
let get_op = snd;;

let trs2rt p = 
 if P.is_sp p then
  let trs = P.get_trs p and s = P.get_strategy p and l = P.get_language p in
  let w = if !(flags.copy) then trs else Trs.empty in
  Some (p,P.make_rp l s trs w)
 else
  None
;;

let rt2trs p = 
 if P.is_rp p then
  let (strict,weak) = P.get_sw p and s = P.get_strategy p and l = P.get_language p in
  if (Trs.is_empty weak || !(flags.force)) then
   Some (p,P.make_sp l s (Trs.union strict weak))
  else
   None
 else
  None
;;

(* Processor *)
let solve fs p =
  let configurate s = F.printf "%s@\n%!" s; flags.help := true in
  (try init (); Arg.parsex code spec fs with Arg.Bad s -> configurate s);
  if !(flags.help) then (Arg.usage spec ("Options for "^code^":"); exit 0);
  M.return (
    if !(flags.inv) then rt2trs p
    else trs2rt p
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

let fprintfx fs p = XO.node "rtTrans" [P.fprintfx (get_op p); List.hd fs];;
