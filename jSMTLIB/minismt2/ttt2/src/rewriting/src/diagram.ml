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
module F = Format;;
module M = Monad;;
module O = Util.Option;;
module Pos = Position;;

(*** OPENS ********************************************************************)
open Prelude;;
open Util;;

(*** MODULES ******************************************************************)
module Make (L : LABEL) = struct
 (*** MODULES *****************************************************************)
 module E = Elogic.Make (L);;
 module M = M.Make (L);;
 (* module Parser = Parser.Make (L);; *)
 (* module Xml = Parser.Xml;; *)
 module S = Signature.Make (L);;
 module Sub = Substitution.Make (L);;
 module Term = Term.Make (L);;
 module Rule = Rule.Make (L);;
 module Trs = Trs.Make (L);;
 module Rewrite = Rewrite.Make (L);;

 (*** TYPES *******************************************************************)
 type 'a m = 'a M.t
 type term = Term.t = Var of Variable.t | Fun of Function.t * term list;;
 type rule = Rule.t;;
 type step = Rewrite.step;;
 type trs = Trs.t;;
 type t = (step list * step) * (step list * step list) list;;
 
 (*** FUNCTIONS ***************************************************************)
 (* Parsers *)
 let (<?>) = Util.(<?>);;
 let (>>=) = M.(>>=);;
 let (>>) = M.(>>);;
 
 (* Iterators *)
 (* Scan Functions *)
 (* Constructors and Destructors *)
 let peak = function
   | (([l],r),_) -> (l,r)
   | _ -> failwith "Diagram.peak: parallel peak"
 ;;
 let par_peak (p,_) = p;;
 let joins (_,js) = js;;
 let make (l,r) js = (([l],r),js);;
 let par_make p js = (p,js);;
 let mirror = function
   | (([l],r),js) -> (([r],l) ,List.map Pair.flip js)
   | _ -> failwith "Diagram.mirror: parallel peak"
 ;;
 let source d = Rewrite.step_get_term (snd (par_peak d));;

 (* Compare Functions *)
 let compare = compare;;
 let equal r r' = compare r r' = 0;;

 let critical_pair ((ls,r),_) = Pair.map Rewrite.step_get_reduct (List.last ls,r);;
  
 let par_diagram ?(m=0) trs ((os,r2) as o) =
  Trs.parallel_critical_peak o >>= fun (t,s,u) ->
  (* let t = Rule.rewrite s p r1 in *)
  (* let u = Rule.rewrite s Position.root r2 in *)
  let ls = List.map (fun (r1,p) -> Rewrite.step_make trs s p r1) os in
  let r = Rewrite.step_make trs s Position.root r2 in
  if m < 0 then (*do not try to join*)
   M.return (Some (par_make (ls,r) []))
  else
   try
   let js = Option.the (Rewrite.min_joins ~m:m t u trs) in
   let ss = List.map (Pair.map (Rewrite.sequence trs)) js in
   M.return (Some (par_make (ls,r) ss))
   with
    | Failure "no content" -> M.return None
 ;;

 let diagram ?(m=0) trs (r1,p,r2) = par_diagram ~m:m trs ([(r1,p)],r2);;

 let critical_diagrams ?(m=0) trs = 
  Trs.overlaps trs trs >>= fun os ->
  M.map (diagram ~m:m trs) os >>= fun ds ->
  try
   M.return (Some (List.map Option.the ds))
  with
   | Failure "no content" -> M.return None
 ;;
 
 let par_critical_diagrams ?(m=0) trs = 
  Trs.parallel_overlaps ~outer:false trs trs >>= fun os ->
  let os = List.filter (fun (ls,_) -> List.length ls > 1) os in
  M.map (par_diagram ~m:m trs) os >>= fun ds ->
  try
   M.return (Some (List.map Option.the ds))
  with
   | Failure "no content" -> M.return None
 ;;
 
 let join_map f j = Pair.map (List.map f) j;;

 (*apply function f to all steps in [d]*)
 let map f ((ls,r),js) = 
  let p = (List.map f ls,f r) in
  let js = List.map (join_map f) js in
  par_make p js
 ;;
 
 (* label a diagram *)
 let rec mapl_seq f n = function
  | [] -> (n,[])
  | s::ss -> 
    let n,s = f n s in
    let n,ss = mapl_seq f n ss in
    (n,s::ss)
 ;;
 
 let mapl_j f nl nr (ls,rs) = 
  let _,ls = mapl_seq f nl ls in
  let _,rs = mapl_seq f nr rs in
  (ls,rs)
 ;;
  
 let mapl f n d = 
  let (ls,r) = par_peak d in
  let nl,_ = mapl_seq f n ls in
  let ls = List.map (Pair.snd <.> f n) ls in
  let nr,r = f n r in
  let js = List.map (mapl_j f nl nr) (joins d) in
  (par_make (ls,r) js)
 ;;

 let label label_step n d = mapl (label_step d) n d;;
 let map f d =  mapl (fun n s -> (~-1,f s)) (~-1) d;;

 (*test decreasingness*)

 let lex_ge = Order.is_ge <.> Order.lex;;
 let lex_gt = Order.is_gt <.> Order.lex;;

 let fsts = List.map Triple.fst;;
 let snds = List.map Triple.snd;;
 let flips = List.map (fun (a,b,i) -> (b,a,i));;

 let is_decreasing_l_strict =
  List.for_all (fun l -> lex_gt (fsts l) || lex_gt (snds l))
 ;;

 let rec is_decreasing_l = function
  | [] -> true
  | l::ls when lex_gt (fsts l) -> is_decreasing_l ls
  | l::ls when lex_ge (snds l) -> is_decreasing_l_strict ls
  | ls -> is_decreasing_l_strict ls
 ;;

 let is_decreasing_s dec sel ss = 
  dec (List.map (sel <.> Rewrite.step_get_lab) ss)
 ;;

 let is_decreasing_j dec (ls,rs) =
  is_decreasing_s dec id    ls &&
  is_decreasing_s dec flips rs
 ;;

 let is_decreasing_aux dec d = 
  List.exists (is_decreasing_j dec) (joins d)
  ;;

 let is_decreasing d = is_decreasing_aux is_decreasing_l d;;
 let is_decreasing_strict d = is_decreasing_aux is_decreasing_l_strict d;;

 let step_get_vars x =
  Term.vars (Term.subterm (Rewrite.step_get_pos x) (Rewrite.step_get_reduct x))
 ;;

 let take_join_steps n js = List.map (Pair.map (List.take n)) js;;
 
 let take ?(n = max_int) d = make (peak d) (take_join_steps n (joins d));;
 

 (* test parallel decreasingness *)

 (* Collect a parallel step <= beta. Note the role of [plab]: Labels in
  * parallel steps are computed with respect to the source of the parallel
  * step, which differs from the source of the same step in the given
  * rewrite sequence. [plab] computes the label of the re-rooted step. *)
 let rec is_par_decreasing_p plab sel vs ps = function
 | [] -> true
 | x::xs when List.for_all (Position.are_parallel (Rewrite.step_get_pos x)) ps
  -> if (lex_ge (snds (sel (Rewrite.step_get_lab (plab x)))) &&
         List.is_subset (step_get_vars x) vs) ||
        lex_gt (snds (sel (Rewrite.step_get_lab x)))
     then is_par_decreasing_p plab sel vs (Rewrite.step_get_pos x::ps) xs
     else is_decreasing_l_strict (List.map (sel <.> Rewrite.step_get_lab) (x::xs))
 | xs -> is_decreasing_l_strict (List.map (sel <.> Rewrite.step_get_lab) xs)
 ;;

 let rec is_par_decreasing_l f n sel vs = function
 | [] -> true
 | x::xs when lex_gt (fsts (sel (Rewrite.step_get_lab x))) ->
  is_par_decreasing_l f (Pair.fst (f n x)) sel vs xs
 | (x::_) as xs ->
  let s = Rewrite.step_get_term x in
  let plab x = Pair.snd (f n (Rewrite.step_set_term s x)) in
  is_par_decreasing_p plab sel vs [] xs
 ;;

 let is_par_decreasing_j f nl nr vs (ls,rs) =
  is_par_decreasing_l f nl id    [] ls &&
  is_par_decreasing_l f nr flips vs rs
 ;;

 let is_par_decreasing f n d =
  let f = f d in
  let (ls,r) = par_peak d in
  let s = Rewrite.step_get_term r in
  (* collect variables for variable condition *)
  let vs = List.unique_hash (List.flat_map
   (fun l -> Term.vars (Term.subterm (Rewrite.step_get_pos l) s)) ls) in
  let (nl,_) = mapl_seq f n ls and (nr,_) = f n r in
  List.exists (is_par_decreasing_j f nl nr vs) (joins d)
 ;;

 let is_inner_parallel_closed trs s t = List.mem t (Rewrite.parallel trs s);;
 let is_outer_parallel_closed trs s t = 
  List.intersect (Rewrite.parallel trs s) (Rewrite.parallel trs t) <> []
 ;;

 let is_parallel_closed trs d = 
 let (l,r) = peak d in
 let (s,t) = Pair.map Rewrite.step_get_reduct (l,r) in
 if Position.is_root (Rewrite.step_get_pos l) then
  is_outer_parallel_closed trs s t
 else
  is_inner_parallel_closed trs s t
 ;;

 let is_strongly_closed_left ?(n=(~-1)) trs s t =
  List.intersect (Rewrite.reducts ~n:n s trs) (Rewrite.reducts ~n:1 t trs) <> [] 
 ;;

 let is_strongly_closed ?(n=(~-1)) trs d =
 let (l,r) = peak d in
 let (s,t) = Pair.map Rewrite.step_get_reduct (l,r) in
 if Position.is_root (Rewrite.step_get_pos l) then
  is_strongly_closed_left ~n:n trs s t
 else
  is_strongly_closed_left ~n:n trs s t && 
  is_strongly_closed_left ~n:n trs t s
 ;;

 let one2many d = List.map (fun join -> par_make (par_peak d) [join]) (joins d);;
 let many2one ds = par_make (par_peak (List.hd ds)) (List.flat_map joins ds);;
 
 let filter p d = many2one (List.filter p (one2many d));;

 let compare_short d1 d2 =
  let [(ls1,rs1)] = joins d1 in
  let [(ls2,rs2)] = joins d2 in
  compare (List.length (ls1@rs1)) (List.length (ls2@rs2))
 ;;

 let find p d = List.hd (List.sort compare_short (one2many (filter p d)));;
 
 (*
 (* Printers *)
 let fprintf fmt r =
  (* F.fprintf fmt "@[%a@ ->@ %a@]" Term.fprintf (lhs r) Term.fprintf
  (rhs r) *)
  ();
 ;;
*)

 let fprintfm_peak fmt d = 
  let (ls,r) = par_peak d in
  M.iter (fun l ->
   Term.fprintfm fmt (Rewrite.step_get_reduct l) >>= fun _ ->
   F.fprintf fmt " <-%d|%a[%a]- " 
    (Rewrite.step_get_rule_idx l)
    Position.fprintf (Rewrite.step_get_pos l)
    Rewrite.fprintf_lab (Rewrite.step_get_lab l);
   M.return ())
   (List.rev ls) >>= fun _ ->
  Rewrite.fprintfm_step ~reduct:true fmt r
 ;;

 let fprintfm_join fmt (ls,rs) = 
  Rewrite.fprintfm_sequence fmt ls >>= fun _ ->
  Format.fprintf fmt "@\n";
  Rewrite.fprintfm_sequence fmt rs >>= fun _ ->
  M.return ();
 ;;

 let fprintfm_joins fmt d = 
  M.iteri (fun i j -> 
   if i > 0 then Format.fprintf fmt "@\n---@\n";
   fprintfm_join fmt j >>= fun _ -> M.return ()) (joins d)
  ;;

 let fprintfm fmt d =
  F.fprintf fmt "@[@[<1>peak:@\n";
  fprintfm_peak fmt d >>= fun _ ->
  F.fprintf fmt "@]@\n";
  F.fprintf fmt "@[<1>joins (%d):@\n" (List.length (joins d));
  fprintfm_joins fmt d >>= fun _ ->
  F.fprintf fmt "@]@]";
  M.return ();
 ;;

(*
 let to_string = F.flush_str_formatter <.> fprintf F.str_formatter;;

 let to_stringm r =
  (* fprintfm F.str_formatter r >>= (M.return <.> F.flush_str_formatter) *)
  M.return ();
 ;; 
 *)
end
