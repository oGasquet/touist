(* $Id: ops.ml,v 1.5 2010/06/21 15:04:13 hzankl Exp $ *)

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

(*** OPENS ********************************************************************)
open Util;;

(*** TYPES ********************************************************************)
(*** FUNCTIONS ****************************************************************)
let (<+>) x y = SmtFormula.Add[x;y]
let (<->) x y = SmtFormula.Sub[x;y]
let (<*>) x y = SmtFormula.Mul[x;y]
let (<&>) x y = SmtFormula.And[x;y]
let (<|>) x y = SmtFormula.Or[x;y]
let (<->>) x y = SmtFormula.Implies(x,y)
let (<<->>) x y = SmtFormula.Iff[x;y]
let const x = SmtFormula.Const x
let neg x = SmtFormula.Not(x)
let top = SmtFormula.Top
let bot = SmtFormula.Bot
let ite x a b = SmtFormula.Ite (x,a,b)

let big op d xs = if xs = [] then d else List.foldl1 op xs;;
let big_add xs = big (<+>) (const Int64.zero) xs;;
let big_sub xs = match xs with
 | [] -> const Int64.zero
 | [x] -> (const Int64.zero) <-> x
 | [x;y] -> x <-> y
;;
let big_mul xs = big (<*>) (const Int64.one) xs;;
let big_and xs = big (<&>) top xs;;
let big_or xs = big (<|>) bot xs;;
let big_iff xs = big (<<->>) top xs;;
