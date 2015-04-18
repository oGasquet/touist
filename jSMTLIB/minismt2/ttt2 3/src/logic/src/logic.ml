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
open Logicx;;
module Number = Number;;
module State = State;;
module Monad = Monad;;
module Formula = Formula;;
module Assignment = Assignment;;
module MiniSat = MiniSat;;
module Yices = Yices ;;
module BinNumber = BinNumber;;
module Operators = Operators;;
module MiniSatP = MiniSatP;;
(*overwrite standard modules with util*)
module H = Util.Hashtbl;;
module List = Util.List;;

(*** OPENS ********************************************************************)
open Operators;;

(*** TYPES ********************************************************************)
type a = Formula.a;;
type arith = Formula.arith = {
  min  : Int64.t;  (** minimal value that must be representable *)
  neg  : bool; (** negative values allowed *)
  rat  : int;  (** denumerator for rational values *)
  real : bool; (** use reals *)
  minf : bool; (** -infinity value allowed *)
};;

type p = Formula.p;;
type assignment = Solver.assignment;;
(*type assignment = Assignment.t;;*)
type core = Formula.a list * bool * (?fprintf_a:(Format.formatter ->
 Formula.a -> unit) -> Format.formatter -> unit);;
type t = Solver.solver * (core option, Assignment.t) Util.either;;

type solver = Solver.solver = MiniSat | MiniSatP | MiniSmt of string list |
Yices | PicoSat ;;

(*** FUNCTIONS ****************************************************************)
let nat n = 
 {min = Int64.of_int n; neg = false; rat = 1; real = false; minf = false};;
let int n = 
 {min = Int64.of_int n; neg = true ; rat = 1; real = false; minf = false};;

let (>>=) = Monad.(>>=);;
let return = Monad.return;;
let run ?(dbits=max_int) ?(obits=max_int) = Monad.run (State.init dbits obits);;

let bot = Formula.bot;;
let top = Formula.top;;
let zero = Formula.zero;;
let one = Formula.one;;
let minus_one = Formula.constant (Number.of_int ~-1);;
let minf = Formula.minf;;
let constant = Formula.constant;;
let of_int n = Formula.constant (Number.of_int n);;

let neg = Formula.(~!);;
let xor = Formula.xor;;
let ite = Formula.ite;;
(*
let min a b = Formula.ite (a <<>b) a b;; 
let max a b = Formula.ite (a <>>b) a b;; 
*)
let min = Formula.min;;
let max = Formula.max;;
let scale a x = Formula.(<*>) (constant a) x;;

let fprintf_p = Formula.fprintf_p;;
let fprintf_a = Formula.fprintf_a;;
let to_string_a = Formula.to_string_a;;
let to_string_p = Formula.to_string_p;;
let fprintf_smt = Formula.fprintf_smt;;
let fprintf_smt2 = Formula.fprintf_smt2;;

let fresh_bool  = Monad.fresh_bool;;
let fresh_arith = Monad.fresh_arith;;

let cache_bool tbl k = 
 if not (Hashtbl.mem tbl k) then
  fresh_bool >>= (fun v ->
  Hashtbl.add tbl k v; return v)
 else return (Hashtbl.find tbl k)
;;

let cache_arith tbl arith k =
 if not (Hashtbl.mem tbl k) then
  fresh_arith arith >>= (fun v ->
  Hashtbl.add tbl k v; return v)
 else return (Hashtbl.find tbl k)
;;
let get_spec = Formula.get_spec;;
let update_spec = Formula.update_spec;;
let variables = Formula.variables;;

let solve = Solver.solve;;
let solve2 = Solver.solve2;;
let eval_a = Solver.eval_a;;
let eval_p = Solver.eval_p;;

let get_assignment = function
 | x, Util.Right ass -> Some (x, ass)
 | _ -> None
;;
let get_unsat_core = function
 | _, Util.Left x -> x
 | _ -> None
;;

let big_and = Formula.big_and;;
let big_or = Formula.big_or;;
let big_sum = Formula.big_sum;;

let obits n x = Formula.obits n x;;

let fresh a = Formula.Fresh a;;

let fprintf_assignment = Solver.fprintf_assignment;;
let set_print_formula = Formula.set_print_formula;;
let set_print_stat = Formula.set_print_stat;;

(*temporary*)
let negate_assignment (_, ass) = Assignment.negate_assignment ass;;

let test () = run (
 let a = BinNat.of_nat (Int64.of_int 2) in
 let b = BinNat.of_nat (Int64.of_int 3) in
 Format.printf "[2] = %s@\n" (BinNat.to_string a);
 BinNat.mul a a >>= fun d ->
 Format.printf "[([2]*[2])] = %s@\n" (BinNat.to_string d);
 BinNat.scale (Int64.of_int 2) a >>= fun d ->
 Format.printf "[(scale 2 [2])] = %s@\n" (BinNat.to_string d);
 BinNat.scale (Int64.of_int 6) a >>= fun d ->
 Format.printf "[(scale 6 [2])] = %s@\n" (BinNat.to_string d);
 return top);
 ()
;;
