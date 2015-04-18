(* $Id: bvReal2.ml,v 1.4 2010/06/13 16:01:04 hzankl Exp $ *)

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
let (<+>) x y = SMT.Add [x;y];;
let (<->) x y = SMT.Sub[x;y];;
let (<*>) x y = SMT.Mul[x;y];;
let ite p x y = SMT.Ite(p,x,y);;

let (<&>) x y = SMT.And [x;y];;
let (<|>) x y = SMT.Or [x;y];;
let (<=>) x y = SMT.Eq(x,y);;
let (<>=>) x y = SMT.Ge(x,y);;
let (<>>) x y = SMT.Gt(x,y);;
let (<<>) = flip (<>>);;
let (<<=>) = flip (<>=>);;
let smtzero = SMT.Const (Int64.of_int 0);;

let s_const ctx c n m = (SMT.Const c::List.replicate (n-1) smtzero,m);;
let zero ctx n m = s_const ctx (Int64.of_int 0) n m;;

let s_add ctx (xs,m) (ys,m') = assert (m = m');
 (List.map2 (<+>) xs ys, m);;
let s_sub ctx (xs,m) (ys,m') = assert (m = m');
 (List.map2 (<->) xs ys, m);;

let rec (>>) (xs,m) i = 
 if i = 0 then (xs,m) 
          else (((m <*> List.last xs)::List.init xs),m) >> (i-1)
;;

let (<.>) (xs,m) y = (List.map (flip (<*>) y) xs,m);;

let s_mul ctx a (ys,m') = assert (snd a = m');
 let n = List.length ys in
 List.foldri (fun i d -> s_add ctx ((a <.> d) >> i)) (zero ctx n m') ys
;;
 
let s_ite ctx p (xs,m) (ys,m') = assert (m = m');
 (List.map2 (ite p) xs ys,m);;

(*
(*approach with subtraction*)
let s_gt ctx a b =
 let ([c1;c2],m) = s_sub ctx a b in
 let c op = op (c1<*>c1) (c2<*>c2<*>m) in
 let phi = c (<>>) and chi = c (<<>) in
 ((c1 <>=> smtzero) <&> (c2 <>=> smtzero) <&> ((c1<>>smtzero) <|> (c2 <>> smtzero))) <|>
 ((c1 <>=> smtzero) <&> (c2 <<> smtzero) <&> phi) <|>
 ((c1 <<> smtzero) <&> (c2 <>=> smtzero) <&> chi)
;;
*)

(*approach w/o subtraction*)
let s_gt ctx ([c1;c2],m) ([d1;d2],m') = assert (m = m');
 let two = SMT.Const (Int64.of_int 2) in
 let c op = op ((c1<*>c1) <+> (d1<*>d1) <+> (two<*>c2<*>d2<*>m))
               ((c2<*>c2<*>m) <+> (d2<*>d2<*>m) <+> (two<*>c1<*>d1)) in
 let phi = c (<>>) and chi = c (<<>) in
 ((c1 <>> d1) <&> (d2 <<=> c2)) <|>
 ((c1 <>=> d1) <&> (d2 <<> c2)) <|>
 ((c1 <>=> d1) <&> (d2 <>=> c2) <&> phi) <|>
 ((c1 <<=> d1) <&> (d2 <<=> c2) <&> chi)
;;

let s_eq ctx (xs,m) (ys,m') = assert (m = m');
 List.foldr (<&>) SMT.top (List.map2 (<=>) xs ys)
;;

let s_ge ctx a b = s_gt ctx a b <|> s_eq ctx a b;;

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
let radical_var = SMT.Vara ("__radical");;
(* let radical_var = SMT.Const (Int64.of_int 3);; *)

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
  | SMT.Const c -> s_const ctx c 2 radical_var
  (* | (SMT.Vara a) as x -> (rat_var x, real_var x) *)
  | (SMT.Vara a) as x -> ([rat_var x;real_var x],radical_var)
  | SMT.Add [a;b] -> s_add ctx (tfac a) (tfac b)
  | SMT.Sub [a;b] -> s_sub ctx (tfac a) (tfac b)
  | SMT.Mul [a;b] -> s_mul ctx (tfac a) (tfac b)
  | SMT.Ite (x,a,b) -> s_ite ctx (tfbc x) (tfac a) (tfac b)
 (* and tfac a = B.cache ctx.B.a_tbl tfa a *)
 (* and tfbc b = B.cache ctx.B.b_tbl tfb b *)
 and tfac a = tfa a
 and tfbc b = tfb b
 in
 SMT.And [SMT.Gt(radical_var,SMT.Const (Int64.of_int 1)); tfb f]
;;

let unzip (SMT.Vara x) = x;;
let ef (a,t) = [(unzip (rat_var (SMT.Vara a)),t); (unzip (real_var (SMT.Vara a)),t)];;

let efs efs = (unzip radical_var, "Int")::List.flat_map ef efs;;

let tf ctx ipt = 
 let ipt = {ipt with SMT.extrafuns = efs ipt.SMT.extrafuns} in
 let ipt = {ipt with SMT.assumptions = List.map (tf ctx) ipt.SMT.assumptions} in
 let ipt = {ipt with SMT.formula = tf ctx ipt.SMT.formula} in
 ipt
;;

let assoc l elt = try List.assoc l elt with Not_found -> Number.zero;;
let tf_back ef va = 
 List.map (fun (v,_) -> 
  let rat0,rat1 = Number.to_rat (assoc (unzip (rat_var (SMT.Vara v))) va) in
  let rea0,rea1 = Number.to_rat  (assoc (unzip (real_var (SMT.Vara v))) va) in
  let obi x = int_of_string (Big_int.string_of_big_int x) in
  let radical = obi (fst (Number.to_rat (assoc (unzip radical_var) va))) in
  (v,Number.of_big_real ~base:radical (rat0,rat1) (rea0,rea1) ))
 ef
;;

let tf_back ctx ef = function
 | None -> None
 | Some (va,vb) -> Some (tf_back ef va ,vb);;
