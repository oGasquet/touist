(* $Id: bitvector.ml,v 1.31 2010/06/24 11:17:09 hzankl Exp $ *)

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
module H = Hashtbl;;
module F = Format;;
module B = Bv;;
module BvReal = BvReal2;;
module SMT = SmtFormula;;
module Number = Logic.Number;;

(*** OPENS ********************************************************************)
open Util;;

(*** GLOBALS*******************************************************************)

(*** TYPES ********************************************************************)
type yt = Bool | Int | Real | BV of int

(*** FUNCTIONS ****************************************************************)
(*set operations according to domain*)
module BO = BvRat;;
let s_gt    = BO.s_gt ;;
let s_ge    = BO.s_ge ;;
let s_eq    = BO.s_eq ;;
let s_add   = BO.s_add;;
let s_sub   = BO.s_sub;;
let s_mul   = BO.s_mul;;
let s_ite   = BO.s_ite;;
let s_const = BO.s_const;;

(*transform SMT formula into bitvectors*)
let tf ctx f =
 let rec tfb = function
  | SMT.Top -> B.Top
  | SMT.Bot -> B.Bot
  | SMT.Varb x -> B.Varb x
  | SMT.Not x -> B.Not (tfbc x)
  | SMT.And [x;y] -> B.And (tfbc x,tfbc y)
  | SMT.Or [x;y] -> B.Or (tfbc x,tfbc y)
  | SMT.Implies (x,y) -> B.Implies(tfbc x,tfbc y)
  | SMT.Iff [x;y] -> B.Iff (tfbc x,tfbc y)
  | SMT.Gt (a,b) -> s_gt ctx (tfac a) (tfac b)
  | SMT.Ge (a,b) -> s_ge ctx (tfac a) (tfac b)
  | SMT.Eq (a,b) -> s_eq ctx (tfac a) (tfac b)
 and tfa = function
  | SMT.Const n -> s_const ctx n
  | SMT.Vara a -> (B.Vara a,ctx.B.rt)
  | SMT.Add [a;b] -> s_add ctx (tfac a) (tfac b)
  | SMT.Sub [a;b] -> s_sub ctx (tfac a) (tfac b)
  | SMT.Mul [a;b] -> s_mul ctx (tfac a) (tfac b)
  | SMT.Ite (x,a,b) -> s_ite ctx (tfbc x) (tfac a) (tfac b)
 and tfac a = B.cache ctx.B.a_tbl tfa a
 and tfbc b = B.cache ctx.B.b_tbl tfb b
 in
 tfb f
;;

let set_denominator ctx d (n,b) = 
 (List.map (fun (x,n) -> (x,Logic.Number.div n d)) n,b)
;;
let filter_aux_vars (n,b) = (List.filter (fun (x,_) -> not (B.is_aux_var x)) n,b);;

let process ctx ass = 
 let d = Logic.Number.of_int ctx.B.rt in
 let ass = Option.map filter_aux_vars ass in
 Option.map (set_denominator ctx d) ass;
;;

(*TODO: yices does not (necessarily) print all variables*)
let get_result ctx cin = 
 let lexbuf = Lexing.from_channel cin in
 let ass = Bvparser.parse Bvlexer.token lexbuf in
 process ctx ass
;;

(* interfacing begin *)
module Y = Yinterface2;;
type ytx = {
  con : Y.yices_context;
  vars : (string,Y.yices_var_decl * yt) H.t;
  ta_tbl : (B.a, Y.yices_expr) H.t;
  tb_tbl : (B.b, Y.yices_expr) H.t;
};;

let init () = 
 Y.yices_enable_type_checker (1);
 (* Y.yices_set_verbosity(10); *)
 {
   con = Y.yices_mk_context ();
   vars = H.create 512;
   ta_tbl = H.create 512;
   tb_tbl = H.create 512;
 };;

let vars ytx = H.fold (fun v (_,t) acc -> (v,t)::acc) ytx.vars [];;
let avars ytx = List.map fst (List.filter (fun (v,t) -> match t with BV _ -> true | _ -> false) (vars ytx));;
let bvars ytx = List.map fst (List.filter (fun (v,t) -> t = Bool) (vars ytx));;

let finalize ytx = 
 Y.yices_del_context ytx.con;
 H.clear ytx.vars;
;;

let decl t ytx x = 
 if not (H.mem ytx.vars x) then begin
  let ty = match t with
   | Bool -> Y.yices_mk_type ytx.con "bool" 
   | Int -> Y.yices_mk_type ytx.con "int"
   | BV n -> Y.yices_mk_bitvector_type ytx.con n
  in
  let xdecl = Y.yices_mk_var_decl ytx.con x ty in
  H.add ytx.vars x (xdecl, t);
 end;
;;

let var t ytx x =
 if not (H.mem ytx.vars x) then decl t ytx x;
 Y.yices_mk_var_from_decl ytx.con (fst (H.find ytx.vars x))

let var_p = var Bool;;
let var_a ctx ytx x =
 let l = B.length ctx (B.Vara x) in 
 let r = var (BV l) ytx x in
 r
;;

let args x y = let a = Array.make 2 x in a.(0) <- x; a.(1) <- y; a;;

(* to and from bits conversion *)
let two = Int64.of_int 2;; 
let rec bits n = 
 if n = Int64.zero then [0]
 else if n = Int64.one then [1]
 else (Int64.to_int (Int64.rem n two))::bits (Int64.div n two)
;;
let bits n = 
 assert (n >= Int64.zero);
 let bs = (bits n) in
 (*
 Debug.debug (Format.sprintf "%s = [%s]" 
  (Int64.to_string n) (List.join string_of_int "," bs));
 *)
 Array.of_list bs
;;

let rec from_bits = function
 | [] -> Int64.zero
 | x::xs -> Int64.add (Int64.of_int x) (Int64.mul two (from_bits xs))
;;

let flip = function
 | 1 -> 0
 | 0 -> 1
;;

let from_bits ng bits =
 (*Debug.debug (Format.sprintf "[%s]" (List.join string_of_int "," bits));*)
 if ng && List.last bits = 1 
  then Int64.neg (Int64.succ (from_bits (List.map flip (bits))))
  else from_bits bits
;;

let value ctx ytx m x = 
 let (decl, t) = H.find ytx.vars x in
 match t with
  | Int -> Number.of_int (Y.helper_get_int_value m decl)
  | Bool -> Number.of_int (Y.helper_get_value m decl)
  | Real -> (* rat is subsumed by real *)
   Number.of_big_rat (Big_int.big_int_of_int (Y.helper_get_num_value m decl)) 
                     (Big_int.big_int_of_int (Y.helper_get_dnum_value m decl))
  | BV l -> 
   let bv = List.gen (Y.helper_get_bitvector_bit m decl l) l in
   Number.of_64_int (from_bits ctx.B.ng bv)
  (*Number.of_int 
   (if ctx.B.ng then Y.helper_get_bitvector_neg_value m decl l
    else Y.helper_get_bitvector_value m decl l)
  *)
;;

(* comparisons *)
let eq ytx a b = Y.yices_mk_eq ytx.con a b;;
let ge ctx ytx a b = 
 if ctx.B.ng then Y.yices_mk_bv_sge ytx.con a b
 else Y.yices_mk_bv_ge ytx.con a b
;;
let gt ctx ytx a b = 
 if ctx.B.ng then Y.yices_mk_bv_sgt ytx.con a b 
 else Y.yices_mk_bv_gt ytx.con a b
;;

let ite ytx c t e = Y.yices_mk_ite ytx.con c t e;;

(* boolean operators *)
let bot ytx = Y.yices_mk_false ytx.con;;
let top ytx = Y.yices_mk_true ytx.con;;
let conj ytx x y = Y.yices_mk_and ytx.con (args x y) 2;;
let disj ytx x y = Y.yices_mk_or ytx.con (args x y) 2;;
let neg ytx x = Y.yices_mk_not ytx.con x;;
let impl ytx x y = disj ytx (neg ytx x) y;;
let iff ytx x y = conj ytx (impl ytx x y) (impl ytx y x);;

(* arithmetic *)
let rec const ctx ytx x = 
 Y.yices_mk_bv_constant_from_array ytx.con (B.length ctx (B.const x)) 
 (bits x);;

let add ytx x y = Y.yices_mk_bv_add ytx.con x y;;
let sub ytx x y = Y.yices_mk_bv_sub ytx.con x y;;
let mul ytx x y = Y.yices_mk_bv_mul ytx.con x y;;

let ex ytx t f a = Y.yices_mk_bv_extract ytx.con t f a;;
let se ytx l a = Y.yices_mk_bv_sign_extend ytx.con a l;;
let ze ytx l a = 
 let zeros = Y.yices_mk_bv_constant ytx.con l 0 in
 Y.yices_mk_bv_concat ytx.con zeros a
;;
 
(*transform SMT formula into bitvectors*)
let tfbv ctx ytx f =
 let rec tfb = function
  | B.Top -> top ytx
  | B.Bot -> bot ytx
  | B.Varb x -> var_p ytx x
  | B.Not x -> neg ytx (tfbc x)
  | B.And (x,y) -> conj ytx (tfbc x) (tfbc y)
  | B.Or (x,y) -> disj ytx (tfbc x) (tfbc y)
  | B.Implies (x,y) -> impl ytx (tfbc x) (tfbc y)
  | B.Iff (x,y) -> iff ytx (tfbc x) (tfbc y)
  | B.Gt (a,b) -> gt ctx ytx (tfac a) (tfac b)
  | B.Ge (a,b) -> ge ctx ytx (tfac a) (tfac b)
  | B.Eq (a,b) -> eq ytx (tfac a) (tfac b)
 and tfa = function
  | B.Const n -> const ctx ytx n
  | B.Vara a -> var_a ctx ytx a 
  | B.Add (a,b) -> add ytx (tfac a) (tfac b)
  | B.Sub (a,b) -> sub ytx (tfac a) (tfac b)
  | B.Mul (a,b) -> mul ytx (tfac a) (tfac b)
  | B.Ite (x,a,b) -> ite ytx (tfbc x) (tfac a) (tfac b)
  | B.Extract (t,f,a) -> ex ytx t f (tfac a)
  | B.Zero_extend (l,a) -> if l = 0 then tfac a else ze ytx l (tfac a)
  | B.Sign_extend (l,a) -> if l = 0 then tfac a else se ytx l (tfac a)
 and tfac a = B.cache ytx.ta_tbl tfa a
 and tfbc b = B.cache ytx.tb_tbl tfb b 
 in
 tfb f
;;
   
let big_and1 = List.foldl1 (fun acc x -> B.And(x,acc));;

let bool_of_number n = match (int_of_string (Number.to_string n)) with | 0 -> false | 1 -> true;;

let solve_smt_interfaced ctx ipt assms phi = 
 let ytx = init () in
 let f = big_and1 (assms@[phi]) in
 Debug.debug "enter interfaced BV SMT solving";
 ignore (Y.yices_assert ytx.con (tfbv ctx ytx f));
 let r = Y.yices_check_aux ytx.con in
 Debug.debug "BV SMT formula solved";
 if r = ~-1 then None else (
  let m = Y.yices_get_model ytx.con in
  let va = avars ytx in
  let va = List.map (fun v -> (v, value ctx ytx m v)) va in
  let vb = bvars ytx in
  let vb = List.map (fun v -> (v, bool_of_number (value ctx ytx m v))) vb in
  process ctx (Some (va,vb))
 );;

(* interfacing end *)

let solve_smt ctx ipt assms phi =
 let (nameout, chout) = Filename.open_temp_file "tmp" ".smt" in
 let namein = Filename.temp_file "tmp" ".smt" in
 let fileout = Format.formatter_of_out_channel chout in
 F.fprintf fileout "%!%a@\n%!" (B.fprintf_smt ctx ipt assms) phi;
 (*TODO: timeout does not work if yices is called via Unix.system *)
 Unix.system ("../ttt2/src/logic/src/yices/bin/yices -smt -e " ^ nameout ^ " > " ^ namein); 
 let chin = Unix.in_channel_of_descr (Unix.openfile namein [Unix.O_RDONLY] 0o660) in
 Debug.debug (Format.sprintf "out-file: %s" nameout);
 Debug.debug (Format.sprintf "in: %s" namein);
 if not !(Debug.on) then (
  ignore (Unix.system ("rm " ^ nameout));
  ignore (Unix.system ("rm " ^ namein));
 );
 get_result ctx chin
;;

let solve ib ob rat db real neg ipt =
 Debug.debug "solve by bitvectors";
 let ctx = B.get_ctx ib ob neg rat real db in
 let ef = ipt.SMT.extrafuns and ep = ipt.SMT.extrapreds in
 Debug.debug (F.sprintf "%d/%d arith/boolean vars" (List.length ef) (List.length ep));
 Debug.debug (F.sprintf "%d in/ %d out-bits standard" ctx.B.ib ctx.B.ob);
 let ipt = if ctx.B.rl then BvReal.tf ctx ipt else ipt in
 let ctx = B.set_specs ctx ipt in
 let assms = List.map (tf ctx) ipt.SMT.assumptions in
 let phi = tf ctx ipt.SMT.formula in
 (*order does matter*)
 let assms = B.get_side_constraint ctx @ assms in
 let solve = if !B.bvi then solve_smt_interfaced else solve_smt in
 let ass = solve ctx ipt assms phi in
 if ctx.B.rl then BvReal.tf_back ctx ef ass else ass
;;
