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
  inv : bool ref;
  parallel : bool ref;
  strongly : int ref;
  trivial : bool ref;
 };;

type t = {
 ip : P.t;
 op : P.t;
 pparallel : bool;
 pstrongly : int;
 ptrivial : bool;
}
(*** GLOBALS ******************************************************************)
let code = "closed";;
let name = "Closedness Processor";;
let keywords = ["closed";"critical pairs";"confluence"];;
let comment = "Tests if critical pairs are XY closed.";;
let flags = {
  help = ref false;
  inv = ref false;
  parallel = ref false;
  strongly = ref ~-1;
  trivial = ref false;
};;

let spec =
 let spec = [
  ("--help",Arg.Set flags.help,"Prints information about flags.");
  ("-help",Arg.Set flags.help,"Prints information about flags.");
  ("-h",Arg.Set flags.help,"Prints information about flags.");
  ("-inv",Arg.Set flags.inv,"Check CPs closed from right-to-left (not known to be sound).");
  ("-parallel",Arg.Set flags.parallel,"Check CPs parallel closed (w/ Toyama refinement).");
  ("-strongly",Arg.Set_int flags.strongly,"Check CPs strongly closed (in <= n steps).");
  ("-trivial",Arg.Set flags.trivial,"Check CPs trivially closed.");
  ] in
 Arg.alignx 80 spec
;;

let help = (comment,keywords,List.map Triple.drop_snd spec);;

(*** FUNCTIONS ****************************************************************)
let make p q = {
 ip = p;
 op = q;
 pparallel = !(flags.parallel);
 pstrongly = !(flags.strongly);
 ptrivial = !(flags.trivial);
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
 if p.pparallel then Format.fprintf fmt " (*parallel*)";
 if p.pstrongly > 0 then Format.fprintf fmt " (*strongly -- <=%d steps*)" p.pstrongly;
 if p.ptrivial then Format.fprintf fmt " (*trivial*)";
;;

let fprintf fs fmt p =
 F.fprintf fmt "@[<1>%s%a:@\n" name fprintf_proof p;
 P.fprintfm fmt (get_op p) >>= fun _ ->
 F.fprintf fmt "@\n"; List.hd fs fmt >>= fun _ -> Monad.return (F.fprintf fmt "@]")
;;

let fprintfx fs p =
  if p.ptrivial then
    XO.node "orthogonal" []
  else  if p.pparallel then 
    XO.node "parallelClosed" []
  else (* if p.strongly then *)
    XO.int "stronglyClosed" p.pstrongly
;;

(*** MODULES (part 2) *********************************************************)
(*** FUNCTIONS ****************************************************************)
let init _ = 
 flags.help   := false;
 flags.inv := false;
 flags.parallel := false;
 flags.strongly := ~-1 ;
 flags.trivial := false;
;;

let closed ?(inv=false) check p = 
 let trs = P.get_trs p in
 let cds = P.get_cds p in
 let cds = if inv then List.map Diagram.mirror cds else cds in
 if List.for_all (check trs) cds then
  let q = P.set_labeling [] (P.set_cds [] p) in
  let q = P.set_strict Trs.empty q in
  Some (make p q)
 else None
;;

let trivial p =
 let trivial_peak d = let (l,r) = Diagram.peak d in
   Rewrite.step_get_reduct l = Rewrite.step_get_reduct r in
 if List.for_all trivial_peak (P.get_cds p) then
  let q = P.set_labeling [] (P.set_cds [] p) in
  let q = P.set_strict Trs.empty q in
  Some (make p q)
 else None
;;

let solve p =
 if P.is_ddp p then (
  let inv = !(flags.inv) in
  if !(flags.trivial) then Monad.return (trivial p)
  else
   let check = (*how diagrams are closed*)
    if !(flags.parallel) then Diagram.is_parallel_closed
    else if !(flags.strongly) >= 0 then Diagram.is_strongly_closed ~n:!(flags.strongly)
    else failwith "Closed: option missing"
   in
   Monad.return (closed ~inv:inv check p)
  )
  else Monad.return None
;;

let solve fs p = 
 let configure s = F.printf "%s@\n%!" s; flags.help := true in
 (try init (); Arg.parsex code spec fs with Arg.Bad s -> configure s);
 if !(flags.help) then (Arg.usage spec ("Options for "^code^":"); exit 0);
 solve p 
;;

