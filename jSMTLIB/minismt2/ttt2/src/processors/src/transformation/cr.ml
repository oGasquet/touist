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
  closed: bool ref;
  drop  : bool ref;
  m     : int ref;
  dup   : bool ref;
  redex : bool ref;
  star  : bool ref;
  force : bool ref;
  kb    : bool ref;
  (* orth  : bool ref; *)
  (* worth  : bool ref; *)
  p     : bool ref;
  rt    : bool ref;
 };;

type t = {
 ip : P.t;
 op : P.t;
 pm : int;
 pdup : bool;
 predex : bool;
 pstar : bool;
 pforce : bool;
 pkb : bool;
 (* porth : bool; *)
 (* pworth : bool; *)
 pp : bool;
 prt : bool;
};;

(*** GLOBALS ******************************************************************)
let code = "cr";;
let name = "Church Rosser Transformation Processor";;
let keywords = ["confluence transformation"; "church rosser transformation";"transformation"];;
let flags = {
 help  = ref false;
 drop  = ref false;
 closed= ref false;
 m     = ref 0;
 dup   = ref false;
 redex = ref false;
 star  = ref false;
 force  = ref false;
 kb    = ref false;
 (* orth  = ref false; *)
 (* worth  = ref false; *)
 p     = ref false;
 rt    = ref false;
};;

let comment = "Transform Church Rosser problems in various ways.";;

let spec =
 let spec = [
  ("--help",Arg.Set flags.help,"Prints information about flags.");
  ("-help",Arg.Set flags.help,"Prints information about flags.");
  ("-h",Arg.Set flags.help,"Prints information about flags.");
  ("-closed",Arg.Set flags.closed,"prepares for closedness test of CPs.");
  ("-drop",Arg.Set flags.drop,"experimental: drop critical diagrams.");
  ("-m",Arg.Set_int flags.m,"search for (minimal+m)-length joins.");
  ("-dup",Arg.Set flags.dup,"prove relative termination of DUP.");
  ("-redex",Arg.Set flags.redex,"prove relative termination of REDEX.");
  ("-star",Arg.Set flags.star,"prove relative termination of STAR.");
  ("-force",Arg.Set flags.force,"force success of processor.");
  ("-kb",Arg.Set flags.kb,"return standard problem if CPs joinable.");
  (* ("-orth",Arg.Set flags.orth,"prove confluence by orthogonality."); *)
  (* ("-worth",Arg.Set flags.worth,"prove confluence by weak orthogonality."); *)
  ("-p",Arg.Set flags.p,"print critical diagrams.");
  ("-rt",Arg.Set flags.rt,"prepare relative termination phase.");
 ] in
 Arg.alignx 80 spec
;;

let help = (comment,keywords,List.map Triple.drop_snd spec);;

(*** FUNCTIONS ****************************************************************)
let make p q = Some {
  ip = p;
  pdup = !(flags.dup);
  predex = !(flags.redex);
  pstar = !(flags.star);
  pforce = !(flags.force);
  pkb = !(flags.kb);
  (* porth = !(flags.orth); *)
  (* pworth = !(flags.worth); *)
  pm = !(flags.m);
  pp = !(flags.p);
  prt = !(flags.rt);
  op = q;
};;
let failwithcode code s = failwith (Format.sprintf "%s: %s" code s);;
let (>>=) = M.(>>=);;
let init _ = 
 flags.help := false;
 flags.closed:= false;
 flags.drop := false;
 flags.m    := 0;
 flags.dup  := false;
 flags.redex := false;
 flags.star := false;
 flags.force := false;
 flags.kb   := false;
 (* flags.orth := false; *)
 (* flags.worth := false; *)
 flags.p    := false;
 flags.rt   := false;
;;

(* Destructors *)
let get_ip p = p.ip;;
let get_op p = p.op;;

let compute_dup trs = M.return (Trs.partition Rule.is_duplicating trs)

let of_pos rule pl pr = 
 M.map (Term.spine (Rule.lhs rule)) pl >>= fun cl ->
 M.map (Term.spine (Rule.rhs rule)) pr >>= fun cr ->
 M.return 
  (Trs.of_list (List.map (uncurry Rule.of_terms) (List.product cl cr)))
;;

let of_rule_x rule x = 
 let (pl,pr) = Rule.map (Term.subterm_pos x) rule in
 match pr with
  | [] -> 
   M.return (Trs.empty,Trs.empty)
  | [p] -> of_pos rule pl [p] >>= fun weak ->
   M.return (Trs.empty,weak)
  | pr -> of_pos rule pl pr >>= fun strict ->
   M.return (strict,Trs.empty)
;;

let merge (s0,w0) (s1,w1) = (Trs.union s0 s1,Trs.union w0 w1);;

let of_rule_star rule = 
 Rule.rename rule >>= fun rule ->
 let xl = List.map Term.make_var (Term.vars (Rule.lhs rule)) in
 let e = M.return (Trs.empty,Trs.empty) in
 List.foldr (fun x -> M.liftM2 merge (of_rule_x rule x)) e xl 
;;

let compute_star trs = 
 let e = M.return (Trs.empty,Trs.empty) in
 Trs.fold (fun rule acc -> M.liftM2 merge acc (of_rule_star rule)) e trs 
;;

let of_rule_redex rule = 
 let (l,r) = Rule.to_terms rule in
 let xs = Term.vars r in
 let dups = List.filter (fun x -> Term.count_var x l < Term.count_var x r) xs in
 (Trs.of_list (List.map (fun x -> Rule.of_terms l (Term.make_var x)) dups), Trs.singleton rule)
;;

let compute_redex trs = 
 let e = (Trs.empty,Trs.empty) in
 M.return (Trs.fold (fun rule acc -> merge acc (of_rule_redex rule)) e trs)
;;

let orthogonal trs = M.return (Trs.empty,Trs.empty);;

let worthogonal trs = M.return (Trs.empty,Trs.empty);;

let empty trs = M.return (Trs.empty,Trs.empty);;
let closed trs = M.return (trs, Trs.empty);;

let l cds trs = Trs.is_linear trs;;
let ll cds trs = Trs.is_left_linear trs;;
let ll_empty cds trs = Trs.is_left_linear trs && cds = [];;
let ll_trivial cds trs = 
 let cps = List.map Diagram.critical_pair cds in
 Trs.is_left_linear trs && List.for_all (uncurry Term.equal) cps
;;
let ttrue _ _ = true;;


let apply g f p = 
 let s = P.get_strategy p and l = P.get_language p in
 let trs = P.get_trs p in
 Diagram.critical_diagrams ~m:!(flags.m) trs >>= function
  | None -> M.return None (*not locally confluent*)
  | Some cds -> (
   if g cds trs then 
    f trs >>= fun (strict,weak) ->
    let cds = if !(flags.drop) (*|| !(flags.worth)*) then [] else cds in (*hack*)
    let q = P.make_ddp l s trs strict weak cds in
    M.return (make p q)
   else M.return None
   )
;;

let idem p = 
 let trs = P.get_trs p in
 Diagram.critical_diagrams ~m:!(flags.m) trs >>= function
  | None -> M.return None (*not locally confluent*)
  | Some _ -> M.return (make p (P.make_sp (P.get_language p) (P.get_strategy p) (P.get_trs p)))
;;

(* Processor *)
let solve fs p =
 let configurate s = F.printf "%s@\n%!" s; flags.help := true in
 (try init (); Arg.parsex code spec fs with Arg.Bad s -> configurate s);
 if !(flags.help) then (Arg.usage spec ("Options for "^code^":"); exit 0);
 (* if !(flags.dup) && !(flags.star) then failwithcode code "only one of -dup and -star allowed"; *)
 if P.is_crp p && Trs.is_trs (P.get_trs p) then 
  if !(flags.rt) then
   let q = P.make_aux (P.get_trs p) Trs.empty p in
   M.return (make p q)
  else if !(flags.closed) then apply ttrue closed p
  else if !(flags.force) then apply ttrue empty p
  else if !(flags.kb) then idem p
  (* else if !(flags.orth) then apply ll_empty orthogonal p *)
  (* else if !(flags.worth) then apply ll_trivial worthogonal p *)
  else if !(flags.redex) then apply ll compute_redex p 
  else if !(flags.star) then apply ll compute_star p 
  else if !(flags.dup) then apply ll compute_dup p
  (* else apply l empty p *)
  else M.return None
 else if P.is_ddp p && !(flags.rt) then
  (* FIXME: is this useful? *)
  let l = P.get_language p and s = P.get_strategy p in
  let (strict,weak) = P.get_sw p in
  let q = P.make_rp l s strict weak in
  M.return (make p q)
 else 
  M.return None
;;

(* Complexity Bounds *)
(* let complexity c _ = C.mul c C.constant;; *)

(* Compare Functions *)
let equal p q = P.equal (get_ip p) (get_ip q);;

(* Printers *)
let fprintf_flags fmt p = 
 if p.pdup then Format.fprintf fmt " (dup)"; 
 if p.predex then Format.fprintf fmt " (redex)"; 
 if p.pstar then Format.fprintf fmt " (star)"; 
 if p.pkb then Format.fprintf fmt " (kb)"; 
 (* if p.porth then Format.fprintf fmt " (orthogonal)";  *)
 (* if p.pworth then Format.fprintf fmt " (weakly orthogonal)";  *)
 if p.prt then Format.fprintf fmt " (to relative problem)"; 
;;

let fprintfm_diagrams fmt p = 
 F.fprintf fmt "@\n@[<1>critical peaks: " ;
 if P.is_sp (get_op p) then M.return (F.fprintf fmt "joinable")
 else if P.is_ddp (get_op p) then
  let cds = Problem.get_cds (get_op p) in
  F.fprintf fmt "%d" (List.length cds);
  M.iter (fun d -> Format.fprintf fmt "@\n";
   if p.pp then Diagram.fprintfm fmt d
   else Diagram.fprintfm_peak fmt d) cds >>= fun _ ->
  F.fprintf fmt "@]";
  M.return ()
 else M.return ()
;;

let fprintf fs fmt p =
 F.fprintf fmt "@[<1>%s%a:@\n" name fprintf_flags p; 
 P.fprintfm fmt (get_op p) >>= fun _ ->
 fprintfm_diagrams fmt p >>= fun _ ->
 F.fprintf fmt "@\n"; List.hd fs fmt >>= fun _ ->
 M.return (F.fprintf fmt "@]")
;;

let fprintfx fs p = XO.node "crProof" [
  if P.is_sp (get_op p) then
    XO.node "crKB" [P.fprintfx (get_op p); List.hd fs]
  else
    List.hd fs
]
;;
