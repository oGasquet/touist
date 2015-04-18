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
  cds : bool ref;
  cdsr : int ref;
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
 pcds : bool;
 pcdsr : int;
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
  cds = ref false;
  cdsr = ref max_int;
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
  ("-lstar",Arg.Set flags.lstar,"drop sw if s is empty.");
  ("-dd",Arg.Set flags.dd,"shift diagrams to strict and trs to weak.");
  ("-cds",Arg.Set flags.cds,"shift critical diagram steps to strict and trs to weak.");
  ("-cdsr",Arg.Set_int flags.cdsr,"first cdsr steps of join are used for -cds.");
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
 pcds = !(flags.cds);
 pcdsr = !(flags.cdsr);
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
 if p.pcds   then Format.fprintf fmt " (cds%s)" 
  (if p.pcdsr = max_int then "" else " " ^ string_of_int p.pcdsr ^ " steps");
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
 flags.cds    := false;
 flags.cdsr   := max_int;
 flags.par    := false;
 flags.force  := false;
;;

let lhs_unique s = (* List.unique for safety *)
 List.length (List.unique (Trs.lhs s)) = List.length (Trs.map Rule.lhs s)
;;

let sstar p = 
 let (s,w) = P.get_sw p in
 if lhs_unique s then
  let q = P.set_sw Trs.empty Trs.empty p in
  Monad.return (Some q)
 else
  Monad.return None
;;

let step2rule ?(r=None) s = 
 let r = Option.option Util.id (Rewrite.step_get_term s) r in
 Rule.of_terms r (Rewrite.step_get_reduct s)
;;

let diagram2steps d = 
 let (l,r) = Diagram.peak d in
 let js = List.flat_map (fun (ls,rs) -> ls@rs) (Diagram.joins d) in
 l::r::js
;;

let diagram2rules d = 
(*choose diagram root as starting term*)
 let root = Rewrite.step_get_term (fst (Diagram.peak d)) in
 let r = if !(flags.cds) then Some root else None in
 List.map (step2rule ~r:r) (diagram2steps d);;

let diagrams2trs trs = Trs.of_list (List.flat_map diagram2rules trs);;

(*~cds indicates if diagram root should be source of step*)
let label_dh_function ~cds removed d n s = 
 let r = if cds then Some (Diagram.source d) else None in
 let step = step2rule ~r:r s in
 let m = if Trs.mem step removed then 0 else n in
 let o = if n = 1 then Order.EQ else Order.GT in
 let s = Rewrite.step_add_label ~left:true s (o, o, n) in
 (m,s)
;;

let ldh_label ~cds removed p = 
 let f = label_dh_function ~cds:cds removed in
 let q = P.label_cds f 1 p in
 let q = P.set_sw Trs.empty Trs.empty q in
 Monad.return (Some q)
;;

let ldh p = 
  if P.is_ddp p then 
   let all = diagrams2trs (P.get_cds p) in
   let remaining = P.get_strict p in
   ldh_label ~cds:false (Trs.diff all remaining) p
  else if P.is_auxp p then 
   let q = P.get_inner_problem p in
   let removed = Trs.diff (P.get_strict q) (P.get_strict p) in
   ldh_label ~cds:true removed q
  else failwith "ldh: wrong problem"
;;

let lstar p = 
 assert (Trs.is_empty (P.get_strict p));
 let q = P.set_sw Trs.empty Trs.empty p in
 Monad.return (Some q)
;;

let dd p = 
 let (s,w) = Problem.get_sw p in
 if !(flags.force) || Trs.is_empty s then
  let s = diagrams2trs (P.get_cds p) in
  let w = Problem.get_trs p in
  let q = Problem.set_sw s w p in
  Monad.return (Some q)
 else
  failwith "dup.dd: strict not empty"
;;

let cds p = 
 let (s,w) = P.get_sw p in
 if !(flags.force) || Trs.is_empty s then
  let cds = List.map (Diagram.take ~n:!(flags.cdsr)) (P.get_cds p) in
  let s = diagrams2trs cds in
  let w = Problem.get_trs p in
  let q = Problem.set_sw s w p in
  Monad.return (Some (Problem.make_aux s w q))
 else
  failwith "dup.cds: strict not empty"
;;
 
let par p =
 let trs = Problem.get_trs p in
 (* TODO: filter strict rules. *)
 Diagram.par_critical_diagrams ~m:!(flags.m) trs >>= fun cds ->
 Monad.return (Option.map (fun cds ->
   Problem.add_and_label_cds cds p) cds)
;;

let solve p =
 if P.is_ddp p then (
  if !(flags.sstar) || !(flags.force) || !(flags.par) || Trs.is_empty (fst (P.get_sw p)) then (
   if !(flags.sstar) then sstar p 
   else if !(flags.ldh) then ldh p
   else if !(flags.lstar) then lstar p
   else if !(flags.dd) then dd p
   else if !(flags.cds) then cds p
   else if !(flags.par) then par p
   else Monad.return None
   ) else Monad.return None
  ) >>= fun q -> Monad.return (Option.map (make p) q)
 else if P.is_auxp p then (
  if !(flags.ldh) then ldh p
  else Monad.return None
  ) >>= fun q -> Monad.return (Option.map (make p) q)
 else
  Monad.return None
;;

let solve fs p = 
 let configure s = F.printf "%s@\n%!" s; flags.help := true in
 (try init (); Arg.parsex code spec fs with Arg.Bad s -> configure s);
 if !(flags.help) then (Arg.usage spec ("Options for "^code^":"); exit 0);
 solve p 
;;

