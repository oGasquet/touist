(* $Id: bv.ml,v 1.26 2013/04/11 12:44:48 hzankl Exp $ *)

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

(*TODO: check if fresh variables are indeed fresh *)
(*** MODULES ******************************************************************)
module H = Hashtbl;;
module F = Format;;
module SMT = SmtFormula;;

(*** OPENS ********************************************************************)
open Util;;

(*** GLOBALS*******************************************************************)
let bvcache = ref true;;
let bvi = ref true;

(*** TYPES ********************************************************************)
type var = string;;

(*extends types [a] and [b] from [SmtFormula] by bitvector operations*)
type b = 
 | Bot | Top | Varb of var
 | Not of b | Or of b*b | And of b*b | Implies of b*b | Iff of b*b
 | Eq of a*a | Ge of a*a | Gt of a*a
and a =
 | Const of Int64.t | Vara of var
 | Add of a*a | Sub of a*a | Mul of a*a
 | Extract of int * int * a
 | Zero_extend of int * a
 | Sign_extend of int * a
 | Ite of b * a * a
;;

type spec = {
 sib   : int; (* bits used for arithmetic *)
};;

type ctx = {
 count : int ref;
 vt    : (a,spec) H.t;
 ib    : int;
 ob    : int;
 db    : int;
 ng    : bool;
 rt    : int;  (*denominator*)
 rl    : bool; (*real*)
 (*caching, side_constraints, etc*)
 sc    : b list ref;
 a_tbl : (SMT.a,(a*int)) H.t;
 b_tbl : (SMT.b,b) H.t;
}

(*** FUNCTIONS ****************************************************************)
let cache tbl f i =
 if not (H.mem tbl i) then H.add tbl i (f i);
 H.find tbl i
;;

(*abbreviations for arithmetic operations*)
let unzip (Vara a ) = a;;
let var_prefix = "v__";;
let var_of_int i = var_prefix ^ (string_of_int i);;
let is_aux_var n = String.is_prefix var_prefix n;;

let fresh_a ctx = let x = Vara (var_of_int !(ctx.count)) in incr ctx.count;x

let add x y = Add(x,y);;
let sub x y = Sub(x,y);;
let mul x y = Mul(x,y);;
let ite x a b = Ite(x,a,b);;
let const n = Const(n);;

let gt x y = Gt(x,y);;
let ge x y = Ge(x,y);;
let eq x y = Eq(x,y);;

let ze l a = Zero_extend(l,a);;
let se l a = Sign_extend(l,a);;
let ex t f a = Extract(t,f,a);;

(*contexts and so on*)
let get_ctx ib ob neg rat real db = 
 let sign = if neg then 1 else 0 in (*bits for sign*)
 {
 count = ref 0;
 vt    = H.create 512;
 ib    = ib; (*sign for ib is set in mval function *)
 ob    = ob + sign; (*one bit for the sign*)
 db    = db;
 ng    = neg;
 rt    = rat;
 rl    = real;
 sc    = ref [];
 a_tbl = H.create 512;
 b_tbl = H.create 512;
};;

let add_side_constraint ctx f = ctx.sc := f::!(ctx.sc);;
let get_side_constraint ctx = !(ctx.sc);;

let set_spec ctx v s = H.add ctx.vt v s;;
let get_spec ctx v = 
 try 
 H.find ctx.vt v with
 | Not_found -> 
  Format.eprintf "spec of variable %s not found@\n%!" (unzip v);
  raise Not_found
;;
let spec_of_ctx ctx = {sib = ctx.ib};;
let make_spec ib = {sib = ib};;

let rec length ctx = function
 | Const n -> Pervasives.max 1 (Int.bits_int64 n) 
 | Vara a -> ((get_spec ctx (Vara a)).sib)
 | Extract(t,f,_) -> assert (t >= f); t - f + 1
 | Zero_extend (n,a) -> n + length ctx a
 | Sign_extend (n,a) -> n + length ctx a
;;

let set_specs ctx ipt =
 (* let s = spec_of_ctx ctx in *)
 (* TODO: sub is just a heuristic (a + 20 = 0) is overseen*)
 let sub = ctx.ng in
 (*let sub = SMT.count_sub ipt > 0 in*)
 let global_neg = ref sub in
 List.iter (fun (v,_) -> 
  let mval,_,_,neg = SMT.max_val false ctx.ib ipt.SMT.assumptions v in
  global_neg := !global_neg || neg;
  let sign = if (neg || sub) then 1 else 0 in
  let bits = (Int.bits_int64 mval) + sign in
  let s = make_spec bits  in
  set_spec ctx (Vara v) s;
  if ipt.SMT.assumptions <> [] && !Debug.on then
   Debug.debug (Format.sprintf "%s of length %d, neg %b" 
    (SMT.va2s v) (length ctx (Vara v)) neg);
  ) ipt.SMT.extrafuns;
 let ctx = {ctx with ng = !global_neg} in
 Debug.debug (Format.sprintf "neg : %b, rat : %d, real : %b" 
  ctx.ng ctx.rt ctx.rl);
 ctx
;;

let bits_add ctx m n = Pervasives.max (length ctx m) (length ctx n) + 1;;
let bits_mul ctx m n = (length ctx m) + (length ctx n);;
let bits_comp ctx m n = Pervasives.max (length ctx m) (length ctx n);;

(* printing *)
let fprintf ctx ppf f = 
let fpf_sign ctx = if ctx.ng then "s" else "u" in
let rec fpf_b ppf = function
  | Top -> F.fprintf ppf "true";
  | Bot -> F.fprintf ppf "false";
  | Varb x -> F.fprintf ppf "%a" SMT.vb2f x
  | Not x -> F.fprintf ppf "(not %a)" fpf_b x
  | And (x,y) -> F.fprintf ppf "(and %a %a)" fpf_b x fpf_b y
  | Or (x,y) -> F.fprintf ppf "(or %a %a)" fpf_b x fpf_b y
  | Implies (x,y) -> fpf_b ppf (Or (Not x,y))
  | Iff (x,y) -> F.fprintf ppf "(comp %a %a)" fpf_b x fpf_b y
  | Gt (a,b) -> F.fprintf ppf "(bv%sgt %a %a)" (fpf_sign ctx) fpf_a a fpf_a b
  | Ge (a,b) -> F.fprintf ppf "(bv%sge %a %a)" (fpf_sign ctx) fpf_a a fpf_a b
  | Eq (a,b) -> F.fprintf ppf "(= %a %a)" fpf_a a fpf_a b
and fpf_a ppf = function
  | Const n -> 
   if n >= Int64.zero then F.fprintf ppf "bv%s[%d]" (Int64.to_string n) (length ctx (Const n)) 
   else failwith "const"
  | Vara a -> F.fprintf ppf "%a" SMT.va2f a
  | Add (a,b) -> F.fprintf ppf "(bvadd %a %a)" fpf_a a fpf_a b
  | Sub (a,b) -> F.fprintf ppf "(bvsub %a %a)" fpf_a a fpf_a b
  | Mul (a,b) -> F.fprintf ppf "(bvmul %a %a)" fpf_a a fpf_a b 
  | Ite (x,a,b) -> F.fprintf ppf "(ite %a %a %a)" fpf_b x fpf_a a fpf_a b
  | Extract (t,f,a) -> F.fprintf ppf "(extract[%d:%d] %a)" t f fpf_a a
  | Zero_extend (l,a) -> if l = 0 then fpf_a ppf a else
   F.fprintf ppf "(zero_extend[%d] %a)" l fpf_a a
  | Sign_extend (l,a) -> if l = 0 then fpf_a ppf a else
   F.fprintf ppf "(sign_extend[%d] %a)" l fpf_a a
 in
fpf_b ppf f
;;

let fprintf_ef ctx ppf (v,t) = F.fprintf ppf "(%s BitVec[%d])" v (length ctx (Vara v));;
let fprintf_ep ctx ppf v = F.fprintf ppf "(%s)" v;;
let fprintf_ass ctx ppf ass = F.fprintf ppf ":assumption %a" (fprintf ctx) ass ;;

let fprintf_extrafuns ctx ppf ipt =
 F.fprintf ppf ":extrafuns (%a)@\n" 
  (List.fprintf (fprintf_ef ctx) "@\n") ipt.SMT.extrafuns;
 let aux = List.gen (fun i -> (var_of_int i, "Int")) !(ctx.count) in
 if aux <> [] then 
   F.fprintf ppf ":extrafuns (%a)@\n" (List.fprintf (fprintf_ef ctx)
   "@\n") aux;
;;
let fprintf_extrapreds ctx ppf ipt =
 if ipt.SMT.extrapreds <> [] then 
  F.fprintf ppf ":extrapreds (%a)@\n"
  (List.fprintf (fprintf_ep ctx) "@\n") ipt.SMT.extrapreds;
 ;;
let fprintf_assumptions ctx ppf assms =
 F.fprintf ppf "%a@\n" (List.fprintf (fprintf_ass ctx) "@\n") assms;
;;

let fprintf_smt ctx ipt assms ppf f =
 F.fprintf ppf "(benchmark none@\n";
 F.fprintf ppf ":logic QF_BV@\n";
 fprintf_extrafuns ctx ppf ipt;
 fprintf_extrapreds ctx ppf ipt;
 fprintf_assumptions ctx ppf assms;
 F.fprintf ppf ":formula %a@\n" (fprintf ctx) f;
 F.fprintf ppf ")";
;;

