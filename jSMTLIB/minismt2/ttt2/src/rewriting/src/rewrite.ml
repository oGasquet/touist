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
module M = Monad;;

(*** OPENS ********************************************************************)
open Prelude;;
open Util;;

(*** MODULES ******************************************************************)
module Make (L : LABEL) = struct
 (*** MODULES *****************************************************************)
 module E = Elogic.Make (L);;
 module M = M.Make (L);;
 module Rule = Rule.Make (L);;
 module Sub = Substitution.Make (L);;
 module Term = Term.Make (L);;
 module Trs = Trs.Make (L);;

 (*** TYPES *******************************************************************)
 type 'a m = 'a M.t;;
 type term = Term.t;;
 type rule = Rule.t;;
 type trs = Trs.t;;
 type position = Position.t;;

 type label = Order.t * Order.t * int;;

 type step = {
  term : Term.t;
  pos :  Position.t;
  rule :  Rule.t;
  rule_idx : int;
  lab : label list; (* for decreasing diagrams *)
 };;
 type t = Full;;
 
 (*** FUNCTIONS ***************************************************************)
 let (>>=) = M.(>>=);;
 let (>>) = M.(>>);;

 (*constructors for step*)
 let step_make trs t p r = {
   term = t; 
   pos = p; 
   rule = r;
   rule_idx = List.position (Rule.equal r) (Trs.to_list trs);
   lab = [];
 };;
 let step_clear_lab s = {s with lab = []};;
 let step_set_term t s = {s with term = t};;
 (*accessors for step*)
 let step_get_term s = s.term;;
 let step_get_pos s = s.pos;;
 let step_get_rule s = s.rule;;
 let step_get_lab s = s.lab;;
 let step_add_label ?(left=false) s l = 
  {s with lab = if left then l::s.lab else s.lab@[l]};;
 (*accessors end*)
 (*combined accessors for step*)
 let step_get_redex s =
  Term.subterm (step_get_pos s) (step_get_term s)
 ;;
 let step_get_reduct s = 
  Rule.rewrite (step_get_term s) (step_get_pos s) (step_get_rule s)
 ;;
 let step_get_rule_idx s = s.rule_idx ;;
 (*combined accessors end*)

(*
 let join_get_sequences (ls,rs) = (ls,rs);;
 let join_to_join (ls,rs) = (ls,rs);;
 let sequence_to_steps ss = ss;;
 let sequence_of_steps ss = ss;;
 *)

 let positions_rules trs s t = 
  let rs = Trs.to_list trs in
  let ps = Term.funs_pos s in
  let prs = List.product ps rs in
  List.filter (fun (p,r) -> Rule.rewrites s p r t) prs
 ;;

(*get steps between [s] and [t]*)
 let step trs s t = 
  let prs = positions_rules trs s t in
 (*TODO: give all steps *)
  List.hd (List.map (fun (p,r) -> step_make trs s p r)  prs)
 ;;

 let fprintf_lab2 fmt (l1,l2,i) =
 Format.fprintf fmt "%a%a%d" Order.fprintf l1 Order.fprintf l2 i
 ;;

 let fprintf_lab fmt lab = 
 Format.fprintf fmt "%a" (List.fprintf fprintf_lab2 ",") lab
 ;;

 let fprintfm_step fmt ?(reduct=true) s = 
  Format.fprintf fmt "@[";
  Term.fprintfm fmt (step_get_term s) >>= fun _ ->
  Format.fprintf fmt " -%d|%a[%a]-> " 
   (step_get_rule_idx s)
   Position.fprintf (step_get_pos s) 
   fprintf_lab (step_get_lab s);
  (if reduct then
    Term.fprintfm fmt (step_get_reduct s) >>= fun _ -> M.return ()
  else M.return ()) >>= fun _ ->
  Format.fprintf fmt "@]";
  M.return ();
 ;;

 let fprintfm_sequence fmt = function
  | [] -> M.return ();
  | seq -> 
   Format.fprintf fmt "@[<1>";
   M.iter (fprintfm_step ~reduct:false fmt) (List.init seq) >>= fun _ ->
   fprintfm_step fmt ~reduct:true (List.last seq) >>= fun _ ->
   Format.fprintf fmt "@]";
   M.return ();
 ;;


(*get rewrite sequences *)
 let rec sequence trs = function
  | [] -> []
  | [x] -> []
  | s::t::ts -> step trs s t::sequence trs (t::ts)
 ;;

 let rec parallel trs t = match t with
  | Term.Var _ -> [t]
  | Term.Fun (f,ts) -> 
   let tss = List.times (List.map (parallel trs) ts) in 
   let rs = List.map (fun ts -> Term.Fun (f,ts)) tss in
   List.unique_hash (Trs.rewrite t Position.root trs@rs)
 ;;

 (* Rewrite Strategies *)
 let rec reducts n width acc ts trs = match n with
  | 0 -> acc
  | n ->
   let rs = List.unique_hash (List.flat_map (flip Trs.reducts trs) ts) in
   let rs = if width < 0 then rs else List.take width rs in
   let acc' = acc@ts in
   let ts' = List.diff rs acc' in
   if ts' = [] then acc'
   else reducts (n-1) width (acc'@ts') ts' trs
 ;;

 let reducts ?(s = Full) ?(n = ~-1) ?(width = ~-1) t trs = 
  if s <> Full then failwith "rewrite: strategy not supported";
  reducts n width [] [t] trs
 ;;
 
 (*compute rewrite closure as set of nodes (s,t) if s -> t*)
 (*acc: n-rewrite closure*)
 (*ts: pairs (s,t) obtained in (n-th) iteration*)
 let closure1 trs s = List.map (fun t -> (s,t)) (Trs.reducts s trs);;

 let rec closure n acc ts trs = match n with
  | 0 -> (acc,ts)
  | n ->
   let rs = List.flat_map (fun (_,t) -> closure1 trs t) ts in
   let acc' = acc@ts in
   let ts' = List.diff (List.unique_hash rs) acc' in
   if ts' = [] then (acc',[])
   else closure (n-1) (acc@ts') ts' trs
 ;;

 let extend t cs u ps =
  if t = u then 
   [ps]
  else
   let pre = List.filter (fun (_,q) -> q = u && q <> t) cs in
   List.map (fun (p,_) -> p::ps) pre
 ;;


(* [pps] are paths from [t] to one of [cs] of length at most [n] *)
 let rec paths n t cs pps =
  if n = 0 then 
   List.filter (function p::ps -> p = t) (List.unique_hash pps)
  else
   let pps' = List.flat_map (function p::ps -> extend t cs p (p::ps)) pps in
   paths (n-1) t cs pps'
 ;;

 let sequences ?(s = Full) ?(n = ~-1) ?(width = ~-1) t trs = 
  if s <> Full then failwith "rewrite: strategy not supported";
  let closure1 (t :: _ as ts) = List.map (fun u -> u :: ts) (Trs.reducts t trs) in
  let closure = if width = -1 then List.flat_map closure1 
    else List.take width <.> List.flat_map closure1 in
  let rec seq n tss = tss @ if n = 0 then [] else seq (n-1) (closure tss) in
  seq n [[t]]
 ;;

 let are_joinable ?(s = Full) ?(n = ~-1) ?(width = ~-1) u v trs = 
  List.intersect (reducts ~n:n ~width:width u trs) (reducts ~n:n ~width:width v trs) <> []
 ;;

 (* find a normal form in a given list of terms *)
 let rec find_normalform ?(n = ~-1) term trs =
  let termlist = term :: reducts ~n:n term trs in
  let is_nf t = Trs.reducts t trs = [] in
  try List.find is_nf termlist with
   Not_found _ -> List.last termlist
 ;;

 (* Checks if term u reaches in n rewrite steps of TRS trs the term v *)
 let is_reachable ?(s = Full) ?(n = ~-1) u v trs = 
  List.mem v (reducts ~s:s ~n:n u trs)
 ;;

 (* Checks if a rule in a TRS is reversible within 10 steps *)
 let is_reversible rule trs = 
  is_reachable ~s:Full ~n:10 (Rule.rhs rule) (Rule.lhs rule) trs
 ;;

 let joins_c n t cs0 u cs1 c =
  let ps0 = paths n t cs0 [[c]] in
  let ps1 = paths n u cs1 [[c]] in
  List.product ps0 ps1
 ;;

 let common cs0 cs1 = 
  List.unique_hash (List.intersect (List.map snd cs0) (List.map snd cs1))
 ;;

 let rec join m n t (cs0,ts0) u (cs1,ts1) trs =
  let cs0 = cs0@ts0 and cs1 = cs1@ts1 in
  let cs = common cs0 cs1 in
  if cs = [] && ts0@ts1 = [] then None (*full search space explored*)
  else if cs <> [] && m <= 0 then Some (List.flat_map (joins_c n t cs0 u cs1) cs)
  else 
   let m = if cs = [] then m else m-1 in (*decrease m if join found*)
   join m (n+1) t (closure 1 cs0 ts0 trs) u (closure 1 cs1 ts1 trs) trs
 ;;

 (* Confluence *)
 let min_joins ?(s = Full) ?(m = 0) t u trs =
  if s <> Full then failwith "rewrite: strategy not supported";
  join m 0 t ([],[(t,t)]) u ([],[(u,u)]) trs
 ;;
 
 let is_wcr ?(s = Full) ?(n = ~-1) r =
  Trs.critical_pairs r r >>= fun cps ->
  M.return (List.for_all (fun (u,v) -> are_joinable ~s:s ~n:n u v r) cps)
 ;;
end
