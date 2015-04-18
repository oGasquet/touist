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
type flags = {fresh : bool ref; help : bool ref};;
type t = P.t * P.t;;

(*** GLOBALS ******************************************************************)
let code = "dp";;
let name = "DP Processor";;
let comment = "Transforms the given TRS into a DP problem.";;
let keywords = ["dp transformation";"termination"];;
let flags = {fresh = ref true; help = ref false};;

let spec =
 let spec = [
  ("--help",Arg.Set flags.help,"Prints information about flags.");
  ("-help",Arg.Set flags.help,"Prints information about flags.");
  ("-h",Arg.Set flags.help,"Prints information about flags.");
  ("-sig",Arg.Clear flags.fresh,"Uses the original symbols as DP symbols.")]
 in
 Arg.alignx 80 spec
;;

let help = (comment,keywords,List.map Triple.drop_snd spec);;

(*** FUNCTIONS ****************************************************************)
let (>>=) = M.(>>=);;
let init _ = flags.fresh := true; flags.help := false;;

(* Destructors *)
let get_ip = fst;;
let get_op = snd;;

(* Processor *)
let generate f trs =
 let ds = Trs.def_symbols trs in
 let generate r m =
  f (Rule.lhs r) >>= fun l ->
  let r = Rule.rhs r in
  let add m r = match Term.root r with
   | Some g when List.mem g ds && not (Term.is_proper_subterm r l) ->
     f r >>= fun r -> m >>= (M.return <.> Trs.add (Rule.of_terms l r))
   | _ -> m
  in
  List.foldl add m (Term.subterms r)
 in
 Trs.fold generate (M.return Trs.empty) trs >>= fun dps ->
 M.return (Some (P.create_dp (Trs.unique dps) trs P.Complete))
;;

let solve fs p =
 let configurate s = F.printf "%s@\n%!" s; flags.help := true in
 (try init (); Arg.parsex code spec fs with Arg.Bad s -> configurate s);
 if !(flags.help) then (Arg.usage spec ("Options for "^code^":"); exit 0);
 if P.is_sp p & Trs.is_trs (P.get_trs p) then
  (if !(flags.fresh) then generate Term.label_dp (P.get_trs p)
  else generate M.return (P.get_trs p)) >>=
  (M.return <.> Option.map (Pair.make p <.> flip P.adapt p))
 else M.return None
;;

(* Complexity Bounds *)
let complexity c _ = C.mul c C.other;;

(* Compare Functions *)
let equal p q = P.equal (get_ip p) (get_ip q);;

(* Printers *)
let fprintf fs fmt p =
 F.fprintf fmt "@[<1>%s:@\n" name; P.fprintfm fmt (get_op p) >>= fun _ ->
 F.fprintf fmt "@\n"; List.hd fs fmt >>= fun _ -> M.return (F.fprintf fmt "@]")
;;

let fprintfx fs prob =
  let op  = get_op prob in
  let dps = P.get_dps op in
  XO.node "dpTrans" [
    P.fprintfx op;
    XO.bool "markedSymbols" true;
    if Trs.is_empty dps
      then XO.node "dpProof" [XO.leaf "pIsEmpty"]
      else List.hd fs
];;
