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

(*** TYPES ********************************************************************)
type flags = {
 help  : bool ref;
 order : bool ref;
 };;

type proof = {
  strict : bool;
  signature : (Function.t * int list * int) list;
  sortorder : (int * int) list;
};;

type t = {
 ip  : P.t;
 ops : P.t list;
 porder : bool;
 proof : proof;
};;

type node =
  | Fun of Function.t         (* return value of f *)
  | Arg of Function.t * int   (* sort of argument i of f *)
  | Var of Variable.t * int;; (* sort of variable v in rule i *)

(* nodes for order-sorted decomposition *)
module Node = struct
  type t = node;;
  let compare = compare;;
  let hash = Hashtbl.hash;;
  let copy n = n;;
  let fprintf fmt = function
    | Fun f -> Format.fprintf fmt "f%a" Function.fprintf f
    | Arg (f, i) -> Format.fprintf fmt "f%a/%i" Function.fprintf f i
    | Var (v, i) -> Format.fprintf fmt "v%a/%i" Variable.fprintf v i;;
end;;

module G = Util.Graph.Make(Node);;
module H = Hashtbl;;

(*** GLOBALS ******************************************************************)
let code = "sorted";;
let name = "Sortedness Decomposition";;
let keywords = ["confluence"; "sortedness decomposition";"transformation"];;
let flags = {
 help  = ref false;
 order = ref false;
};;

let comment = "Decompose a problem due to sort information." ;;

let spec =
 let spec = [
  ("--help",Arg.Set flags.help,"Prints information about flags.");
  ("-help",Arg.Set flags.help,"Prints information about flags.");
  ("-h",Arg.Set flags.help,"Prints information about flags.");
  ("-order",Arg.Set flags.order,"Try order-sorted decomposition.");
 ] in
 Arg.alignx 80 spec
;;

let help = (comment,keywords,List.map Triple.drop_snd spec);;

(*** FUNCTIONS ****************************************************************)
let make p qs proof = Some {
  ip = p;
  porder = !(flags.order);
  ops = qs;
  proof = proof;
};;
let failwithcode code s = failwith (Format.sprintf "%s: %s" code s);;
let (>>=) = M.(>>=);;
let init _ = 
 flags.help := false;
 flags.order := false;
;;

(* Destructors *)
let get_ip p = p.ip;;
let get_ops p = p.ops;;
let get_proof p = p.proof;;

let top i = function
  | Term.Var v -> Var (v, i)
  | Term.Fun (f,_) -> Fun f
;;

(* Find most general sort attachment *)
let attach_sorts strict trs =
 let step rule (i, cs) =
   (* add constraints for a single rule *)
   let lhs = Rule.lhs rule and rhs = Rule.rhs rule in
   let rec inner strict t cs =
     let inner0 ctx t cs =
       let cs' = inner strict t cs and t' = top i t in
       (ctx, t') :: if Term.is_var t && strict then (t', ctx) :: cs' else cs' in
     match t with
       | Term.Var v -> cs
       | Term.Fun (f, ts) -> List.foldli (fun i cs t ->
           inner0 (Arg (f, i)) t cs) cs ts
   in
   if Term.is_var rhs then
     (* collapsing rule *)
     let cs' = inner true lhs cs in
     (i+1, (top i lhs, top i rhs) :: if strict then (top i rhs, top i lhs) :: cs' else cs')
   else
     (* non-collapsing rule *)
     (i+1, (top i lhs, top i rhs) :: inner true (Rule.lhs rule) (inner strict (Rule.rhs rule) cs))
 in
 (* add simple constraints *)
 let (_, cs) = Trs.fold step (0, []) trs in
 (* add maximality constraints *)
 let cs = if not strict then cs else
   let inv = G.transitive_closure (G.make [] (List.map (fun (a, b) -> (b, a)) cs)) in
   let step rule (i, cs) = if not (Rule.is_collapsing rule) then (i+1, cs) else
     let t = top i (Rule.rhs rule) in
     (i+1, List.map (fun n -> (t, n)) (G.successors t inv) @ cs) in
   snd (Trs.fold step (0, cs) trs) in
 (* add syntactical constraints *)
 let funs = Trs.funs trs in
 M.map M.find_ari funs >>= fun ari ->
 let arimap = List.map2 (fun a b -> (a, b)) funs ari in
 let addari cs (f, n) = List.map (fun i -> (Fun f, Arg (f, i))) (List.range 0 n) @ cs in
 let cs = List.foldl addari cs arimap in
 (* solve *)
 let g = G.make [] cs in
 let sccs = G.sccs g in
 let gt = G.transitive_closure g in
 M.return (gt, sccs, arimap)
;;

let bots = function
  | Term.Var v -> failwith "Sorted.bots: variable left-hand side"
  | Term.Fun (f, ts) ->
  let rec bots' i ctx bs = function 
    | Term.Var v -> (v, ctx) :: bs
    | Term.Fun (f, ts) -> 
      List.foldli (fun i -> bots' i (Arg (f, i))) bs ts
  in
  List.foldli (fun i bs ti -> bots' i (Arg (f, i)) bs ti) [] ts
;;

(* Find pairs of nested rules that persistence allows *)
let nested strict trs =
 attach_sorts strict trs >>= fun (ge, _, _) ->
 M.return (flip Trs.flat_map trs (fun r ->
  let bots = bots (Rule.lhs r) in
  flip List.flat_map (Trs.to_list trs) (fun r' ->
   let t = top (-1) (Rule.lhs r') in
   List.unique_hash (
    List.foldl (fun xs (v, b) ->
     if G.mem_edge (b, t) ge then (r,v,r') :: xs else xs
    ) [] bots
   )
  )
 ))
;;

(* Find order-sorted decomposition *)
let order_sorted p = 
 let trs = P.get_trs p in
 let trsl = Trs.to_list trs in
 (* only strictly bind occurrences of variables on rhs for general systems *)
 let strict = not (Trs.is_left_linear trs) && Trs.is_duplicating trs in
 attach_sorts strict trs >>= fun (gt, sccs, arimap) ->
 let candidates = List.map List.hd sccs in
 let es = (List.filter (fun (a, b) -> a <> b) (G.edges (G.restrict candidates gt))) in
 let g' = G.make [] es in
 (* find max sorts *)
 let g'inv = G.make [] (List.map (fun (a, b) -> (b, a)) (G.to_list g')) in
 let max = List.filter (fun n -> List.is_empty (G.successors n g'inv)) candidates in

(*
 Format.printf "---@\n%a@\n" G.fprintf g;
 Format.printf "---@\n[%a]@\n" (List.fprintf (Pair.fprintf Node.fprintf Node.fprintf) ",@\n") es;
 Format.printf "---@\n%a@\n" G.fprintf g';
 Format.printf "---@\n[%a]@\n" (List.fprintf Node.fprintf ",") max;
*)

 (* decompose problems *)
 let select t = List.filter (fun rule -> let t' = top (-1) (Rule.lhs rule) in t = t' || G.mem_edge (t, t') gt) trsl in
 let boring trs = false in (* List.is_empty trs || trs = trsl in *)
 let qs = List.unique (List.filter (not <.> boring) (List.map select max)) in

 (* extract signature *)
 let h = H.of_list (List.foldli (fun i ps scc -> List.map (fun a -> (a, i)) scc @ ps) [] sccs) in
 let signature = flip List.map arimap (fun (f, n) ->
   (f,
    List.map (fun i -> H.find_ (Arg (f, i)) h) (List.range 0 n),
    H.find_ (Fun f) h)) in
 let sortorder = List.concat (List.concat (flip List.map candidates (fun a ->
   flip List.map candidates (fun b ->
     if a <> b && G.mem_edge (a, b) gt then [(H.find_ a h, H.find_ b h)] else [])))) in
 (* remove redundant sortorder constraints *)
 let sortorder' = List.map (fun ((a, b), (c, d)) -> (a,d)) (List.filter (fun ((a,b), (c,d)) -> b = c) (List.product sortorder sortorder)) in
 let sortorder = List.diff sortorder sortorder' in
 if List.length qs > 1 then (*if processor should make progress*)
  let l = P.get_language p and s = P.get_strategy p in
  let qs' = List.map (P.make_crp l s <.> Trs.of_list) qs in
  let proof = make p qs' { strict = strict; signature = signature; sortorder = sortorder } in
  M.return proof
 else
  M.return None
;;

(* Processor *)
let solve fs p =
 let configurate s = F.printf "%s@\n%!" s; flags.help := true in
 (try init (); Arg.parsex code spec fs with Arg.Bad s -> configurate s);
 if !(flags.help) then (Arg.usage spec ("Options for "^code^":"); exit 0);
 if P.is_crp p then
  if !(flags.order) then order_sorted p
  else M.return None
 else 
  M.return None
;;

(* Complexity Bounds *)
let complexity c _ = C.mul c C.constant;;

(* Compare Functions *)
let equal p q = P.equal (get_ip p) (get_ip q);;

(* Printers *)
let fprintf_flags fmt p = 
 if p.porder then Format.fprintf fmt "(order)"; 
;;

let fprintfm_proof fmt p =
  Format.fprintf fmt "sorts@\n";
  let fprintf_pair fmt (a,b) = Format.fprintf fmt "%i>%i" a b in
  Format.fprintf fmt "  @[[%a]@]@\n" (List.fprintf fprintf_pair ",@ ") (p.sortorder);
  Format.fprintf fmt "@[<2>sort attachment (%s)" (if p.strict then "strict" else "non-strict");
  flip M.iter (p.signature) (fun (f, ts, t) ->
    Format.fprintf fmt "@\n";
    M.fprintf_fun fmt f >>= fun _ ->
    if List.is_empty ts then
      Format.fprintf fmt " : %d" t
    else
      Format.fprintf fmt " : %a -> %d" (List.fprintf Int.fprintf " x ") ts t;
    M.return ()
  ) >>= fun _ ->
  Format.fprintf fmt "@]@\n";
  M.return ()
;;

let fprintf fs fmt proof = 
 F.fprintf fmt "@[sorted: %a@\n" fprintf_flags proof;
 M.iteri 
  (fun i p -> 
   F.fprintf fmt "@[<1>%d:" i;
   P.fprintfm fmt p >>= fun _ ->
   F.fprintf fmt "@]@\n";
   M.return ();
   )
  (get_ops proof) >>= fun _ ->
  F.fprintf fmt "-----@\n@[";
  fprintfm_proof fmt (proof.proof) >>= fun _ ->
  F.fprintf fmt "@]";
  let fprintfi i fmt p =
  F.fprintf fmt "%d:@[" i;
  P.fprintfm fmt p >>= fun _ -> 
  F.fprintf fmt "@\n";
  List.nth fs i fmt >>= fun _ ->
  F.fprintf fmt "@]@\n"; 
  M.return ()
 in
 F.fprintf fmt "-----@\n@[";
 M.fprintfi fprintfi "@\n@\n" fmt (get_ops proof) >>= fun _ ->
 F.fprintf fmt "@]@]";
 M.return ();
;;

let fprintfx fs fmt proof =
 failwith "Order: xml proof not supported";
;;
