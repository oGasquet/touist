(* $Id: bvRat.ml,v 1.7 2010/03/10 13:24:52 hzankl Exp $ *)

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
let expand ctx (n0,d0) (n1,d1) =
 let gcd = Int.gcd d0 d1 in
 let a = BvInt.s_scale ctx (Int64.of_int (d1/gcd)) n0 in
 let b = BvInt.s_scale ctx (Int64.of_int (d0/gcd)) n1 in
 (a,b,Int.lcm d0 d1)
;;

let rec cancel ctx (n,d) =
  (* Debug.debug (Format.sprintf "calling cancel (d = %d, db = %d)" d ctx.B.db); *)
 let l = B.length ctx n in
 if Int.bits (d-1) > ctx.B.db (*cancellation applies*) 
  && l > 1 (*numerator can be canceled*)
  && d mod 2 = 0 (*denominator can be canceled*) then (
  (* Debug.debug (Format.sprintf "canceling (d = %d)" d); *)
  B.add_side_constraint ctx (B.eq (B.const Int64.zero) (B.ex 0 0 n));
  cancel ctx (B.ex (l-1) 1 n,d/2)
 ) else (n,d)
;;

(* let cancel ctx a = a;; *)
let perform ctx op a b d =
 let ctx' = {ctx with B.ob = max_int} in
 let (n,d) = cancel ctx (op ctx' a b,d) in
 (BvInt.restrict ctx n,d)
;;

let s_add ctx a b = 
 let a,b,d = expand ctx a b in
 perform ctx BvInt.s_add a b d
;;

let s_sub ctx a b = 
 let a,b,d = expand ctx a b in
 perform ctx BvInt.s_sub a b d
;;

let s_mul ctx (a,na) (b,nb) = 
 perform ctx BvInt.s_mul a b (na*nb)
;;

let s_ite ctx x a b = 
 let a,b,d = expand ctx a b in
 perform ctx (flip BvInt.s_ite x) a b d
;;

let s_gt ctx a b = let a,b,_ = expand ctx a b in
 BvInt.s_gt ctx a b;;
 
let s_ge ctx a b = let a,b,_ = expand ctx a b in
 BvInt.s_ge ctx a b;;
 
let s_eq ctx a b = let a,b,_ = expand ctx a b in
 BvInt.s_eq ctx a b;;

let s_const ctx n = (BvInt.s_const ctx n,1);;

(*wrappers*)
let set2 ctx f0 f1 = 
 if ctx.B.rt <> 1 then f0 ctx else f1 ctx
;;

let wrap2 f ctx a b = (f ctx (fst a) (fst b),1);;
let wrap3 f ctx x a b = (f ctx x (fst a) (fst b),1);;
let wrap f ctx a b = f ctx (fst a) (fst b);;

let s_add ctx = set2 ctx s_add (wrap2 BvInt.s_add);;
let s_sub ctx = set2 ctx s_sub (wrap2 BvInt.s_sub);;
let s_mul ctx = set2 ctx s_mul (wrap2 BvInt.s_mul);;
let s_ite ctx = set2 ctx s_ite (wrap3 BvInt.s_ite);;
let s_gt ctx = set2 ctx s_gt (wrap BvInt.s_gt);;
let s_ge ctx = set2 ctx s_ge (wrap BvInt.s_ge);;
let s_eq ctx = set2 ctx s_eq (wrap BvInt.s_eq);;
let s_const ctx = set2 ctx s_const (fun ctx n -> BvInt.s_const ctx n,1)
(*abbreviations*)
let s_scale ctx n a = s_mul ctx (s_const ctx n) a;;
