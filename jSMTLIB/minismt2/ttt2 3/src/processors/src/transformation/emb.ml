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
module Sig = Signature;;
module XO = XmlOutput;;

(*** TYPES ********************************************************************)
type flags = {
 help : bool ref;
 w : bool ref;
 oldsig : bool ref;
};;
type t = P.t * P.t;;

(*** GLOBALS ******************************************************************)
let code = "emb";;
let name = "Embedding Processor";;
let keywords = ["simple termination";"embedding";"transformation"];;
let flags = {
 help = ref false;
 w = ref false;
 oldsig = ref false;
};;

let comment = "Adds embedding rules to TRS.";;

let spec =
 let spec = [
  ("--help",Arg.Set flags.help,"Prints information about flags.");
  ("-help",Arg.Set flags.help,"Prints information about flags.");
  ("-h",Arg.Set flags.help,"Prints information about flags.");
  ("-oldsig",Arg.Set flags.oldsig,"Use original signature (default: funs in TRS).");
  ("-w",Arg.Set flags.w,"Adds embedding rules in weak component (as relative problem).");
] in
 Arg.alignx 80 spec
;;

let help = (comment,keywords,List.map Triple.drop_snd spec);;

(*** FUNCTIONS ****************************************************************)
let (>>=) = M.(>>=);;
let init _ = flags.help := false;;

(*Monad interaction*)
let arity f = M.get >>= fun state -> M.return (Sig.find_ari f state);;

(* Destructors *)
let get_ip = fst;;
let get_op = snd;;

let emb_f_i f xs i = 
 let ts = List.map Term.make_var xs in
 Trs.of_list [Rule.of_terms (Term.make_fun f ts) (List.nth ts i)]
;;

let emb_f f = 
 arity f >>= fun a ->
 M.get >>= fun t -> 
 let xs = List.gen (fun i -> "x"^string_of_int i) a in
 let add_var xi (xs,t) = let (x,t) = Sig.create_var xi t in (x::xs,t) in
 let xs,t = List.foldr add_var ([],t) xs in
 M.set t >>= fun _ ->
 M.return (List.foldli (fun i trs _ -> Trs.union trs (emb_f_i f xs i)) Trs.empty xs)
;;

let embedding_rules trs = 
 (if !(flags.oldsig) then M.get >>= fun c -> 
 M.return (List.rev (List.map (fun f -> Sig.find_fun f c) (Sig.fun_names c)))
 else M.return (Trs.funs trs)) >>= fun fs ->
 M.sequence (List.map emb_f fs) >>= fun trss ->
 M.return (List.foldl Trs.union Trs.empty trss);;

(* Processor *)
let solve fs p =
  let configurate s = F.printf "%s@\n%!" s; flags.help := true in
  (try init (); Arg.parsex code spec fs with Arg.Bad s -> configurate s);
  if !(flags.help) then (Arg.usage spec ("Options for "^code^":"); exit 0);
  let strict,weak = P.get_sw p in
  embedding_rules (Trs.union strict weak) >>= fun emb ->
  let strict = if !(flags.w) then strict else Trs.union strict emb in
  let weak = if !(flags.w) then Trs.union weak emb else weak in
  let s = P.get_strategy p and l = P.get_language p in
  let make = if P.is_rp p || !(flags.w) then P.make_rp else fun s l strict _ -> P.make_sp s l strict in
  M.return (
    if P.is_sp p || P.is_rp p then Some (p,make l s strict weak) else None
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

let fprintfx fs p = XO.node "embTrans" [P.fprintfx (get_op p); List.hd fs];;
