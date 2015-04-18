(* $Id: bvReal.ml,v 1.4 2010/04/18 13:43:17 hzankl Exp $ *)

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
module SMT = SmtFormula;;
module Number = Logic.Number;;

(*** OPENS ********************************************************************)
open Util;;

(*** GLOBALS*******************************************************************)

(*** TYPES ********************************************************************)
(*** FUNCTIONS ****************************************************************)
let oi n = Int64.of_int n;;

let s_add ctx (a,b) (c,d) = (SMT.Add [a;c], SMT.Add [b;d]);;
let s_sub ctx (a,b) (c,d) = (SMT.Sub [a;c], SMT.Sub [b;d]);;

let s_mul ctx (a,b) (c,d) = 
 (SMT.Add[SMT.Mul[a;c];SMT.Mul[SMT.Const (oi 2);SMT.Mul[b;d]]],
 (SMT.Add[SMT.Mul[a;d];SMT.Mul[b;c]]))
;;

let s_ite ctx x (a,b) (c,d) = (SMT.Ite(x,a,c),SMT.Ite(x,b,d));;

let under b = SMT.Ite(SMT.gt b (SMT.Const (oi 0)),SMT.Const (oi 5), SMT.Const (oi 6));;
let over  d = SMT.Ite(SMT.gt d (SMT.Const (oi 0)),SMT.Const (oi 6), SMT.Const (oi 5));;

let s_gt ctx (a,b) (c,d) = 
 let l0 = SMT.Mul[SMT.Const (oi 4); a] in
 (* let l1 = SMT.Mul[SMT.Const (oi 5); b] in *)
 let l1 = SMT.Mul[under b; b] in
 let r0 = SMT.Mul[SMT.Const (oi 4); c] in
 (* let r1 = SMT.Mul[SMT.Const (oi 6); d] in *)
 let r1 = SMT.Mul[over d; d] in
 SMT.Gt(SMT.Add [l0;l1],SMT.Add [r0;r1])

let s_eq ctx (a,b) (c,d) = 
 SMT.And [SMT.Eq (a,c);SMT.Eq(b,d)]
;;

let s_ge ctx a b = SMT.Or [s_gt ctx a b;s_eq ctx a b];;

let s_const ctx n = (SMT.Const n, SMT.Const (oi 0))

(*wrappers*)
(* let set2 ctx f0 f1 =  *)
 (* if not ctx.B.rl then f0 ctx else f1 ctx *)
(* ;; *)

(* let wrap2 f ctx a b = (f ctx (fst a) (fst b),snd a);; *)
(* let wrap3 f ctx x a b = (f ctx x (fst a) (fst b),snd a);; *)
(* let wrap f ctx a b = f ctx (fst a) (fst b);; *)
(*  *)
(* let s_add ctx = set2 ctx s_add (wrap2 SMT.Add);; *)
(* let s_sub ctx = set2 ctx s_sub (wrap2 BvRat.s_sub);; *)
(* let s_mul ctx = set2 ctx s_mul (wrap2 BvRat.s_mul);; *)
(* let s_ite ctx = set2 ctx s_ite (wrap3 BvRat.s_ite);; *)
(* let s_gt ctx = set2 ctx s_gt (wrap BvRat.s_gt);; *)
(* let s_ge ctx = set2 ctx s_ge (wrap BvRat.s_ge);; *)
(* let s_eq ctx = set2 ctx s_eq (wrap BvRat.s_eq);; *)
(* let s_const ctx = s_const ctx *)
(* (*abbreviations*) *)
(* let s_scale ctx n a = s_mul ctx (s_const ctx n) a;; *)

let rat_var (SMT.Vara a) = SMT.Vara (a^"_rat");;
let real_var (SMT.Vara a) = SMT.Vara (a^"_real");;

let tf ctx f =
 let rec tfb = function
  | SMT.Top -> SMT.Top
  | SMT.Bot -> SMT.Bot
  | SMT.Varb x -> SMT.Varb x
  | SMT.Not x -> SMT.Not (tfbc x)
  | SMT.And [x;y] -> SMT.And [tfbc x;tfbc y]
  | SMT.Or [x;y] -> SMT.Or [tfbc x;tfbc y]
  | SMT.Implies (x,y) -> SMT.Implies(tfbc x,tfbc y)
  | SMT.Iff [x;y] -> SMT.Iff [tfbc x;tfbc y]
  | SMT.Gt (a,b) -> s_gt ctx (tfac a) (tfac b)
  | SMT.Ge (a,b) -> s_ge ctx (tfac a) (tfac b)
  | SMT.Eq (a,b) -> s_eq ctx (tfac a) (tfac b)
 and tfa = function
  | SMT.Const n -> s_const ctx n
  | (SMT.Vara a) as x -> (rat_var x, real_var x)
  | SMT.Add [a;b] -> s_add ctx (tfac a) (tfac b)
  | SMT.Sub [a;b] -> s_sub ctx (tfac a) (tfac b)
  | SMT.Mul [a;b] -> s_mul ctx (tfac a) (tfac b)
  | SMT.Ite (x,a,b) -> s_ite ctx (tfbc x) (tfac a) (tfac b)
 (* and tfac a = B.cache ctx.B.a_tbl tfa a *)
 (* and tfbc b = B.cache ctx.B.b_tbl tfb b *)
 and tfac a = tfa a
 and tfbc b = tfb b
 in
 tfb f
;;

let unzip (SMT.Vara x) = x;;
let ef (a,t) = [(unzip (rat_var (SMT.Vara a)),t); (unzip (real_var (SMT.Vara a)),t)];;

let tf ctx ipt = 
 let ipt = {ipt with SMT.extrafuns = List.flat_map ef ipt.SMT.extrafuns} in
 let ipt = {ipt with SMT.assumptions = List.map (tf ctx) ipt.SMT.assumptions} in
 let ipt = {ipt with SMT.formula = tf ctx ipt.SMT.formula} in
 ipt
;;

let assoc l elt = try List.assoc l elt with Not_found -> Number.zero;;
let tf_back ef va = 
 List.map (fun (v,_) -> 
  let rat0,rat1 = Number.to_rat (assoc (unzip (rat_var (SMT.Vara v))) va) in
  let rea0,rea1 = Number.to_rat  (assoc (unzip (real_var (SMT.Vara v))) va) in
  (v,Number.of_big_real (rat0,rat1) (rea0,rea1) ))
 ef
;;

let tf_back ctx ef = function
 | None -> None
 | Some (va,vb) -> Some (tf_back ef va ,vb);;
