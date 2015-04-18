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
module G = Graph;;
module L = List;;
module M = Monad;;
module Map = Map.Partial (Term);;
module P = Problem;;
module R = Rule;;
module S = Substitution;;
module XO = XmlOutput;;

(*** TYPES ********************************************************************)
type flags = {help : bool ref; i : bool ref; old : bool ref;};;
type t = P.t * bool * P.t;;

(*** GLOBALS ******************************************************************)
let code = "edg";;
let name = "EDG Processor";;
let keywords = ["dependency graph";"approximation";"termination"];;
let flags = {help = ref false; i = ref false; old = ref false};;

let comment =
 "Remove all edges from the current DG that are not contained in the \
  EDG (approximation of DG based on recursive unification and symmetry)."
;;

let spec =
 let spec = [
  ("--help",Arg.Set flags.help,"Prints information about flags.");
  ("-help",Arg.Set flags.help,"Prints information about flags.");
  ("-h",Arg.Set flags.help,"Prints information about flags.");
  ("-i",Arg.Set flags.i,"Computes the innermost EDG, if possible.");
  ("-old",Arg.Set flags.old,"Removes only edges from l->r to l'->r' where \
   ren(cap(r)) is not unifiable with l' (old edg implementation).");
 ] in
 Arg.alignx 80 spec
;;

let help = (comment,keywords,L.map Triple.drop_snd spec);;

(*** FUNCTIONS ****************************************************************)
let (>>=) = M.(>>=);;
let init _ = 
 flags.help := false;
 flags.i := false;
;;

(* Destructors *)
let get_ip = Triple.fst;;
let get_op = Triple.thd;;

(* Processor *)
let is_arc trs ml mr (x,y) =
 let rename = if !(flags.i) then R.rename else M.return in
 let s = R.lhs x and t = R.rhs x and u = R.lhs y and v = R.rhs y in
 rename (R.of_terms s (Map.find t mr)) >>= fun x' ->
 rename (R.of_terms (Map.find u ml) v) >>= fun y' ->
 let s' = R.lhs x' and t' = R.rhs x' and u' = R.lhs y' in
 let root = Option.the <.> Term.root <?> "left-hand side is a variable" in
 if root t = root u then
  if !(flags.i) then
   try
    let sub = Elogic.unify t' u and sub' = Elogic.unify u' t in
    let nf sub t = Trs.is_normal_form (S.apply_term sub t) trs in
    M.return (nf sub s' && nf sub u && nf sub' s)
   with Elogic.Not_unifiable -> M.return (false)
  else (
   if !(flags.old) then
    M.return (Elogic.are_unifiable t' u')
   else
    M.return (Elogic.ground_matches t' u && Elogic.ground_matches u' t)
  )
 else M.return false
;;

let generate trs ml mr ns =
 M.foldl (fun g n -> M.foldl (fun ms m ->
  M.liftM (fun c -> if c then m::ms else ms) (is_arc trs ml mr (n,m))) [] ns >>=
  (M.return <.> flip (G.add n) g)) G.empty ns
;;

let filter_edges trs ml mr g =
 G.fold (fun n ms m -> m >>= fun g ->
  let add m ms c = M.return (if c then m::ms else ms) in
  M.foldl (fun ms m -> is_arc trs ml mr (n,m) >>= add m ms) [] ms >>=
  (M.return <.> flip (G.add n) g)) g (M.return G.empty)
;;

let solve fs p =
 let configurate s = F.printf "%s@\n%!" s; flags.help := true in
 (try init (); Arg.parsex code spec fs with Arg.Bad s -> configurate s);
 if !(flags.help) then (Arg.usage spec ("Options for "^code^":"); exit 0);
 if P.is_dp p then
  let trs = P.get_trs p and dps = P.get_dps p and g = P.next_dg p in
  let g = P.the_graph dps g in
  let (ls,rs) = Pair.map L.unique_hash (Trs.lhs dps,Trs.rhs dps) in
  flags.i := !(flags.i) && P.is_it p;
  (* configurate computation *)
  let modify_lhs = if !(flags.i) then Trs.tcap else 
   if !(flags.old) then (fun l _ -> M.return l) else Trs.etcap in
  let modify_rhs = if !(flags.i) then Trs.icap else 
   if !(flags.old) then Trs.tcap else Trs.etcap in
  let add f m t = f t >>= (M.return <.> flip (Map.add t) m) in
  M.foldl (add (flip modify_rhs trs)) Map.empty rs >>= fun mr ->
  M.foldl (add (flip modify_lhs (Trs.invert trs))) Map.empty ls >>= fun ml ->
  (* compute arcs *)
  filter_edges trs ml mr (G.restrict (Trs.to_list dps) g) >>= fun h ->
  let i = !(flags.i) in
  let progress = not (G.equal h g) in
  let q = P.set_dg (P.Partial h) dps trs p in
  M.return (if progress then Some (p,i,q) else None)
 else M.return None
;;

(* Complexity Bounds *)
let complexity c _ = C.mul c C.other;;

(* Compare Functions *)
let equal p q = P.equal (get_ip p) (get_ip q);;

(* Printers *)
let fprintf fs fmt p =
 F.fprintf fmt "@[<1>%s:@\n" name;
 P.fprintfm ~g:true fmt (get_op p) >>= fun _ ->
 F.fprintf fmt "@\n"; L.hd fs fmt >>= fun _ ->
 M.return (F.fprintf fmt "@]")
;;

let fprintfx fs p = XO.node "depGraphProc" [
  P.fprintfx ~g:true (get_op p);
  List.hd fs];;
