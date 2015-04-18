(* $Id: bvInt.ml,v 1.13 2010/01/03 18:24:52 hzankl Exp $ *)

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
let sign ctx a = let l = B.length ctx a in B.ex (l-1) (l-1) a;;

let restrict ctx c =
 let lc = B.length ctx c and ob = ctx.B.ob in
 if lc <= ob then c else 
  (B.add_side_constraint ctx 
   (B.eq (B.ex (lc-1) (ob-1) c) (B.se (lc-ob) (sign ctx c)));
  B.ex (ob-1) 0 c)
;;

let perform op op_bits ctx a b = 
 let la,lb = B.length ctx a, B.length ctx b in
 let l = op_bits ctx a b in
 let c = B.ex (l-1) 0 (op (B.se (l-la) a) (B.se (l-lb) b)) in

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
 op (B.se (l-la) a) (B.se (l-lb) b)
;;

let s_add ctx a b = perform B.add B.bits_add ctx a b;;
let s_sub ctx a b = perform B.sub B.bits_add ctx a b;;
let s_mul ctx a b = perform B.mul B.bits_mul ctx a b;;

let s_ite ctx x a b = perform (B.ite x) B.bits_comp ctx a b;;

let s_gt ctx a b = perform_bool B.gt B.bits_comp ctx a b;;
let s_ge ctx a b = perform_bool B.ge B.bits_comp ctx a b;;
let s_eq ctx a b = perform_bool B.eq B.bits_comp ctx a b;;

let s_const ctx n = B.ze 1 (B.Const n);; (*constants are non-negative*)

let set2n ctx f0 f1 = (if ctx.B.ng then f0 else f1);;
let set2  ctx f0 f1 = (set2n ctx f0 f1) ctx

(*wrappers*)
let s_add ctx = set2 ctx s_add BvNat.s_add;;
let s_sub ctx = set2 ctx s_sub BvNat.s_sub;;
let s_mul ctx = set2 ctx s_mul BvNat.s_mul;;
let s_ite ctx = set2 ctx s_ite BvNat.s_ite;;
let s_const ctx = set2 ctx s_const BvNat.s_const;;

let s_gt ctx = set2 ctx s_gt BvNat.s_gt;;
let s_ge ctx = set2 ctx s_ge BvNat.s_ge;;
let s_eq ctx = set2 ctx s_eq BvNat.s_eq;;

let restrict ctx = set2 ctx restrict BvNat.restrict;;

(*abbreviations*)
let s_scale ctx n a = 
 let ctx' = {ctx with B.ob = max_int} in
 s_mul ctx' (s_const ctx n) a;;
