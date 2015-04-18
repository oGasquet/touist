(* $Id: bvNat.ml,v 1.18 2010/03/10 13:24:51 hzankl Exp $ *)

(* Copyright 2009 Harald Zankl
 * GNU Lesser General Public License
 *
 * This file is part of MiniSMT.
 * 
 * MiniSMT is free software: you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or (at your
 * option) any later version.
 * 
 * MiniSMT is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public
 * License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with MiniSMT. If not, see <http://www.gnu.org/licenses/>.
 *)

(*** MODULES ******************************************************************)
module B = Bv;;

(*** OPENS ********************************************************************)
open Util;;

(*** GLOBALS*******************************************************************)

(*** TYPES ********************************************************************)
(*** FUNCTIONS ****************************************************************)
let restrict ctx c =
 let l = B.length ctx c and ob = ctx.B.ob in
 if l <= ob then c else (
  B.add_side_constraint ctx (B.eq (B.ex (l-1) ob c) (B.ze (l-ob-1)
  (B.const Int64.zero)));
  B.ex (ob-1) 0 c 
 );;

let perform op op_bits ctx a b = 
 let la,lb = B.length ctx a, B.length ctx b in
 let l = op_bits ctx a b in
 let c = B.ex (l-1) 0 (op (B.ze (l-la) a) (B.ze (l-lb) b)) in

 let d = if !(B.bvcache) then
  let d = B.fresh_a ctx in
  B.set_spec ctx d (B.make_spec l);
  B.add_side_constraint ctx (B.eq c d);
  d
 else c
 in

 restrict ctx d
;;

let perform_bool op op_bits ctx a b = 
 let la,lb = B.length ctx a, B.length ctx b in
 let l = op_bits ctx a b in
 op (B.ze (l-la) a) (B.ze (l-lb) b)
;;

let s_add ctx a b = perform B.add B.bits_add ctx a b;;
let s_sub ctx a b = failwith "BvNat.sub: not possible";;
let s_mul ctx a b = perform B.mul B.bits_mul ctx a b;;

let s_ite ctx x a b = perform (B.ite x) B.bits_comp ctx a b;;

let s_gt ctx a b = perform_bool B.gt B.bits_comp ctx a b;;
let s_ge ctx a b = perform_bool B.ge B.bits_comp ctx a b;;
let s_eq ctx a b = perform_bool B.eq B.bits_comp ctx a b;;

let s_const ctx n = B.Const(n);;
