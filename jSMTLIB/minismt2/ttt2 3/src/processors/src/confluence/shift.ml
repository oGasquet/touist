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
module Fun = Function;;
module P = Problem;;
module Var = Variable;;
module XO = XmlOutput;;

(*** TYPES ********************************************************************)
type flags = {
  help : bool ref;
  sstar : bool ref;
  ldh : bool ref;
  lstar : bool ref;
  dd : bool ref;
  par : bool ref;
  force : bool ref;
  m : int ref;
 };;
type t = {
 ip : P.t;
 op : P.t;
 psstar : bool;
 pldh : bool;
 plstar : bool;
 pdd : bool;
 ppar : bool;
 pforce : bool;
}
(*** GLOBALS ******************************************************************)
let code = "shift";;
let name = "Shift Processor";;
let keywords = ["shift";"decreasing diagrams";"confluence"];;
let comment = "Shifts strict rules to weak rules if lhs is unique.";;
let flags = {
  help = ref false;
  sstar = ref false;
  ldh = ref false;
  lstar = ref false;
  dd = ref false;
  par = ref false;
  force = ref false;
  m = ref 0;
};;

let spec =
 let spec = [
  ("--help",Arg.Set flags.help,"Prints information about flags.");
  ("-help",Arg.Set flags.help,"Prints information about flags.");
  ("-h",Arg.Set flags.help,"Prints information about flags.");
  ("-sstar",Arg.Set flags.sstar,"drop sw if lhss of s unique.");
  ("-ldh",Arg.Set flags.ldh,"drop sw and label diagrams with dh wrt sw.");
  ("-lstar",Arg.Set flags.lstar,"drop sw.");
  ("-dd",Arg.Set flags.dd,"shift diagrams to strict and trs to weak.");
  ("-par",Arg.Set flags.par,"extend diagrams to parallel peaks.");
  ("-m",Arg.Set_int flags.m,"search for (minimal+m)-length joins.");
  ("-force",Arg.Set flags.force,"apply even if strict not empty.");
  ] in
 Arg.alignx 80 spec
;;

let help = (comment,keywords,List.map Triple.drop_snd spec);;

(*** FUNCTIONS ****************************************************************)
let make p q = {
 ip = p;
 op = q;
 psstar = !(flags.sstar);
 pldh = !(flags.ldh);
 plstar = !(flags.lstar);
 pdd = !(flags.dd);
 ppar = !(flags.par);
 pforce = !(flags.force);
};;

let (>>=) = Monad.(>>=);;
(* Destructors *)
let get_ip p = p.ip;;
let get_op p = p.op;;

(* Complexity Bounds *)
(* let complexity c _ = C.mul c C.constant;; *)

(* Compare Functions *)
let equal p q =
 P.equal (get_ip p) (get_ip q) && P.equal (get_op p) (get_op q)
;;

(* Printers *)
let fprintf_proof fmt p = 
 if p.psstar then Format.fprintf fmt " (**)";
 if p.pldh   then Format.fprintf fmt " (ldh)";
 if p.plstar then Format.fprintf fmt " (no label)"
             else Format.fprintf fmt " lab=left";
 if p.pdd    then Format.fprintf fmt " (dd)";
 if p.ppar   then Format.fprintf fmt " (par)";
 if p.pforce then Format.fprintf fmt " (force)";
;;

let fprintf fs fmt p =
 F.fprintf fmt "@[<1>%s%a:@\n" name fprintf_proof p;
 P.fprintfm fmt (get_op p) >>= fun _ ->
 F.fprintf fmt "@]@\n"; List.hd fs fmt >>= fun _ -> Monad.return (F.fprintf fmt "@]")
;;

let fprintfx fs p = XO.node "shift" [P.fprintfx (get_op p); List.hd fs];;

(*** MODULES (part 2) *********************************************************)
(*** FUNCTIONS ****************************************************************)
let init _ = 
 flags.help   := false;
 flags.sstar  := false;
 flags.ldh    := false;
 flags.lstar  := false;
 flags.dd     := false;
 flags.par    := false;
 flags.force  := false;
;;

let lhs_unique s = (* List.unique for safety *)
 List.length (List.unique (Trs.lhs s)) = List.length (Trs.map Rule.lhs s)
;;

let sstar p = 
 let (s,w) = P.get_sw p in
 if lhs_unique s && not (Trs.is_empty s) then
  let q = P.set_sw Trs.empty Trs.empty p in
  Monad.return (Some q)
 else
  Monad.return None
;;

let label_dh remaining n s = 
 let m = if Trs.mem (Rewrite.step_get_rule s) remaining then n else max 0 (n-1) in
 let s = Rewrite.step_add_label ~left:true s n in
 (m,s)
;;

let ldh p = 
 let (s,w) = Problem.get_sw p in
 let f = label_dh (Trs.union s w) in
 let q = P.label_cds f 1 p (*TODO: determine progress *) in
 let q = P.set_sw Trs.empty Trs.empty q in
 Monad.return (Some q)
;;

let lstar p = 
 let q = P.set_sw Trs.empty Trs.empty p in
 Monad.return (Some q)
;;

let diagram2steps d = 
 let (l,r) = Diagram.peak d in
 let js = List.flat_map (fun (ls,rs) -> ls@rs) (Diagram.joins d) in
 l::r::js
;;

let step2rule s = 
 Rule.of_terms (Rewrite.step_get_term s) (Rewrite.step_get_reduct s)
;;

let diagram2rules d = List.map step2rule (diagram2steps d);;

let diagrams2trs trs = Trs.of_list (List.flat_map diagram2rules trs);;

let dd p = 
 let (s,w) = Problem.get_sw p in
 if !(flags.force) || Trs.is_empty s then
  let s = diagrams2trs (Problem.get_cds p) in
  let w = Problem.get_trs p in
  let q = Problem.set_sw s w p in
  Monad.return (Some q)
 else
  failwith "dup.dd: strict not empty"
;;

let par p =
 let trs = Problem.get_trs p in
 (* TODO: filter strict rules. *)
 Diagram.par_critical_diagrams ~m:!(flags.m) trs >>= fun cds ->
 Monad.return (Option.map (fun cds ->
   Problem.add_cds cds p) cds)
;;

let solve p =
 if P.is_ddp p then (
  if !(flags.sstar) || !(flags.force) || !(flags.par) || Trs.is_empty (fst (P.get_sw p)) then (
   if !(flags.sstar) then sstar p 
   else if !(flags.ldh) then ldh p
   else if !(flags.lstar) then lstar p
   else if !(flags.dd) then dd p
   else if !(flags.par) then par p
   else Monad.return None
   ) else Monad.return None
  ) >>= fun q -> 
   Monad.return (Option.map (make p) q)
   else
   Monad.return None
;;

let solve fs p = 
 let configure s = F.printf "%s@\n%!" s; flags.help := true in
 (try init (); Arg.parsex code spec fs with Arg.Bad s -> configure s);
 if !(flags.help) then (Arg.usage spec ("Options for "^code^":"); exit 0);
 solve p 
;;

