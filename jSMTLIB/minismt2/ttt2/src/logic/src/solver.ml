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
open Monad;;
open Formula;;
open Util;;

(*** FUNCTIONS ****************************************************************)
type solver = MiniSat | MiniSatP | MiniSmt of string list | Yices | PicoSat | Gpw of string list;;
type assignment = (solver * Assignment.t)

let eval_a a = function
 | (Yices, ass) -> Yices.eval_a a ass
 | (MiniSat, ass) -> MiniSat.eval_a a ass
 | (PicoSat, ass) -> MiniSat.eval_a a ass
 | (MiniSatP, ass) -> return (MiniSatP.eval_a a ass)
 | (MiniSmt _, ass) -> MiniSmt.eval_a a ass
 | (Gpw _, ass) -> return (Gpw.eval_a a ass)
;;

let eval_p p = function
 | (Yices, ass) -> Yices.eval_p p ass
 | (MiniSat, ass) -> MiniSat.eval_p p ass
 | (PicoSat, ass) -> MiniSat.eval_p p ass
 | (MiniSatP, ass) -> return (MiniSatP.eval_p p ass)
 | (MiniSmt _, ass) -> MiniSmt.eval_p p ass
 | (Gpw _, ass) -> return (Gpw.eval_p p ass)
;;

let fprintf_assignment ppf (_, ass) = Assignment.fprintf ppf ass

(* experimental begin *)

let rec sub acc ms =
 let (p,n) = List.hd (foo ms) in
 if n < 2 then return (ms,acc) else (
  let spec = a_spec (unwrap_a (fst p)) in
  fresh_arith spec >>= fun n ->
  Format.printf "%s -> %s@\n%!" (to_string_pair p) (to_string_a n);
  (*let ms = substitute p n ms in*)
  let ms = substitute p n ms in
  sub ((p,n)::acc) ms 
);;

let sub0 p n acc ms =
 let spec = a_spec (unwrap_a (fst p)) in
 fresh_arith spec >>= fun n ->
 Format.printf "%s -> %s@\n%!" (to_string_pair p) (to_string_a n);
 let ms = substitute p n ms in
 return ((p,n)::acc,ms)
;;

(*
let rec sub pn ms = 
 let ps = foo ms in
 let p,n = List.hd ps in
 if n < 2 then return (ms,pn)
 else sub0 p n pn ms >>= fun (pn,ms) -> 
  sub pn ms
;;
*)

let rec sub pn ms = 
 let ps = foo ms in
 let p,n = List.hd ps in
 if n < 2 then return (ms,pn)
 else 
  List.foldr (fun (p,n) acc -> acc >>= fun (pn,ms) ->
   sub0 p n pn ms) (return (pn,ms)) ps >>= fun (pn,ms) -> 
  sub pn ms
;;

(* experimental end *)

let solve2 ?(solver=MiniSat) ?(goal=None) ?(cnf=false) f =
 (*Format.printf "formula = %a@\n" Formula.fprintf_p f;*)
 (*
 let f = nf2 (nfb f) in
 let ms = get_mulb f in
 sub [] (List.map m_as_list ms) >>= fun (ms',sigma) ->
 let f = List.foldl (fun acc (mi,[si]) -> apply mi si acc) f
 (List.combine ms ms') in
 (*
 List.iter (fun (p,n) -> 
  Format.printf "%s -> %s" (to_string_pair p) (to_string_a n)) sigma;
 Format.printf "@\n";
 *)
 let f = big_and (f::List.map (fun ((a,b),n) -> a <*> b <=> n) sigma) in
 (*Format.printf "formula2 = %a@\n" fprintf_p f;*)
 Format.printf "transformed@\n%!";
 *)
 let either_of_option = function
  | Some x -> return (Right x)
  | _ -> return (Left None) in
 (match solver with
  | PicoSat -> (if cnf then PicoSat.solve_cnf else PicoSat.solve) f
  | MiniSat -> (if cnf then MiniSat.solve_cnf else MiniSat.solve) f >>= either_of_option
  | MiniSatP -> MiniSatP.solve ~goal:goal f >>= either_of_option
  | Gpw flags -> Gpw.solve ~goal:goal ~options:flags f >>= either_of_option
  | MiniSmt flags -> MiniSmt.solve flags f >>= either_of_option
  | Yices -> Yices.solve f >>= either_of_option
  ) >>= function
   | Right ass ->
     (*for safety reasons formula is checked for satisfiabiliy *)
     eval_p f (solver, ass) >>= fun b -> assert b;
     return (solver, Right ass)
   | Left core -> return (solver, Left core)
;;

let solve ?(solver=MiniSat) ?(goal=None) ?(cnf=false) f =
 solve2 ~solver:solver ~goal:goal ~cnf:cnf f >>= function
  | x, Right ass -> return (Some (x, ass))
  | _ -> return None
;;
