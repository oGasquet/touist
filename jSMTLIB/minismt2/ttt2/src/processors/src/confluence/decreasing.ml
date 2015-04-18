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
open Logic.Operators;;

(*** MODULES ******************************************************************)
module C = Complexity;;
module F = Format;;
module Fun = Function;;
module Number = Logic.Number;;
module P = Problem;;
module Var = Variable;;
module XO = XmlOutput;;

(*** TYPES ********************************************************************)
type flags = {
  help : bool ref;
  strict : bool ref;
  par : bool ref;
 };;

type t = {
 ip : P.t;            (*input problem*)
 dd : Diagram.t list; (*decreasing diagrams*)
 op : P.t;            (*output problem*)
 pstrict : bool;
 ppar : bool;
};;

(*** GLOBALS ******************************************************************)
let code = "decreasing";;
let name = "Decreasing Processor";;
let keywords = ["decreasing";"decreasing diagrams";"confluence"];;
let comment = "Drops critical diagrams if they are decreasing.";;
let flags = {
  help = ref false;
  strict = ref false;
  par = ref false;
};;

let spec =
 let spec = [
  ("--help",Arg.Set flags.help,"Prints information about flags.");
  ("-help",Arg.Set flags.help,"Prints information about flags.");
  ("-h",Arg.Set flags.help,"Prints information about flags.");
  ("-strict",Arg.Set flags.strict,"Drop critical pairs if the are strict decreasing.");
   ("-par",Arg.Set flags.par,"Allow parallel steps.");
 ] in
 Arg.alignx 80 spec
;;

let help = (comment,keywords,List.map Triple.drop_snd spec);;

(*** FUNCTIONS ****************************************************************)
let make ip dd op = Some {
 ip = ip;
 dd = dd;
 op = op;
 pstrict = !(flags.strict);
 ppar = !(flags.par);
};;

let (>>=) = Monad.(>>=);;
(* Destructors *)
let get_ip p = p.ip;;
let get_dd p = p.dd;;
let get_op p = p.op;;
let get_strict p = p.pstrict;;

(* Complexity Bounds *)
let complexity c _ = C.mul c C.constant;;

(* Compare Functions *)
let equal p q =
 P.equal (get_ip p) (get_ip q) && P.equal (get_op p) (get_op q)
;;

(* Printers *)
let fprintf_strict fmt b = if b then F.fprintf fmt "strict " else ();;

let fprintf fs fmt p =
 F.fprintf fmt "@[<1>%s" name; 
 if p.ppar then F.fprintf fmt " (par)";
 F.fprintf fmt ":@\n";
 F.fprintf fmt "The following diagrams are %adecreasing:" fprintf_strict (get_strict p);
 Monad.iter (fun d -> 
  F.fprintf fmt "@\n";
  Diagram.fprintfm fmt d >>= fun _ -> 
  Monad.return ()) (get_dd p) >>= fun _ ->
 F.fprintf fmt "@]@\n"; List.hd fs fmt >>= fun _ -> Monad.return (F.fprintf fmt "@]")
;;

let fprintfx fs p = XO.node "shift" [P.fprintfx (get_op p); List.hd fs];;

(*** MODULES (part 2) *********************************************************)
type context = {
 arith              : Logic.arith;
 rtbl               : (Rule.t,Logic.a) Hashtbl.t;
};;

module Statex = struct type t = context end;;
module M = Util.Monad.Transformer.State (Statex) (Logic.Monad);;
open M;;

(*** FUNCTIONS ****************************************************************)
let (>>=) = M.(>>=);;
let (>>) = M.(>>);;
let init _ = 
 flags.help   := false;
;;

let sequence_labeling d =
 List.foldr (fun (f,n) (fs,ns) ->
  ((fun _ (n::ns) s -> let (ns',s') = fs d ns s in
                     let (n',s'') = f d n s' in
                     ((n'::ns'),s''))),
   (n::ns))
  ((fun _ _ s -> ([],Rewrite.step_clear_lab s)),[])
;;

let solve p =
 if P.is_ddp p then
  let cds = P.get_cds p in 
  let (s,_) = P.get_sw p in
  let decreasing d = if !(flags.par) then 
                      let (f,ns) = sequence_labeling d (P.get_labeling p) in
                      Diagram.is_par_decreasing f ns d
                   else if !(flags.strict) then Diagram.is_decreasing_strict d
                   else Diagram.is_decreasing d in
  if (!(flags.par) || Trs.is_empty s) && cds <> [] && List.for_all decreasing cds then
   let dd = List.map (Diagram.find decreasing) cds in
   make p dd (P.set_labeling [] (P.set_cds [] (P.set_strict Trs.empty p)))
  else None
 else None
;;

let solve fs p = 
  let configure s = F.printf "%s@\n%!" s; flags.help := true in
  (try init (); Arg.parsex code spec fs with Arg.Bad s -> configure s);
  if !(flags.help) then (Arg.usage spec ("Options for "^code^":"); exit 0);
(*
  let (>>=) = Monad.(>>=) in
  Monad.iter (fun d -> Format.printf "@\n"; Diagram.fprintfm Format.std_formatter d) (P.get_cds p) >>= fun _ ->
  Format.printf "@\n";
*)
  Monad.return (solve p)
;;

