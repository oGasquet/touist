(* $Id: smtFormula.ml,v 1.64 2013/07/03 06:56:03 hzankl Exp $ *)

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
module L = Logic;;
module H = Hashtbl;;
module Number = Logic.Number;;

(*** OPENS ********************************************************************)
open Util;;
open Logic.Operators;;

(*** GLOBALS ******************************************************************)
let infer = ref false;;

(* let solver = ref Logic.PicoSat;; *)
let solver = ref Logic.MiniSat;;
let set_comp_solver _ = solver := Logic.MiniSat;;
let set_solver s =
 match String.lowercase s with
 | "picosat" -> solver := Logic.PicoSat
 | "minisat" -> solver := Logic.MiniSat
 | "minisatp" -> solver := Logic.MiniSatP
 | "yices" -> solver := Logic.Yices
;;

type refine_bits_op = AddB of Int64.t | MulB of Int64.t;;
let set_refine_bits x s =
 match String.to_char_list s with
 | '+'::tl -> x := AddB (Int64.of_string (String.of_char_list tl))
 | '*'::tl -> x := MulB (Int64.of_string (String.of_char_list tl))
;;
let refine_ib = ref (MulB (Int64.of_int 2));;
let refine_ob = ref (AddB (Int64.of_int 2));;

(*** TYPES ********************************************************************)
type assignment = ((string * L.Number.t) list * (string * bool) list);;
type back = UNKNOWN | UNSAT | SAT of assignment;;

type var = string;;

type b = 
 | Bot | Top | Varb of var
 | Not of b | Or of b list | And of b list | Implies of b * b | Iff of b list
 | Eq of a * a | Ge of a * a | Gt of a * a
 (* | Let of var * a * b *)
and a =
 | Const of Int64.t | Vara of var
 | Add of a list | Sub of a list | Mul of a list
 | Ite of b * a * a
;;

type typ = string;;

type smt = {
 benchmark   : string;
 difficulty  : string;
 logic       : string;
 status      : string ;
 source      : string;
 category    : string;
 info        : string list;
 extrafuns   : (var*typ) list;
 extrapreds  : var list;
 assumptions : b list;
 formula     : b
}

let empty = {
 benchmark = "unknown";
 logic = "unknown";
 difficulty = "unknown";
 status = "unknown";
 source = "unknown";
 category = "unknown";
 info     = [];
 extrafuns = [];
 extrapreds = [];
 assumptions = [];
 formula = Bot;
};;

let set_benchmark d s = {s with benchmark = d};;
let set_difficulty d s = {s with difficulty = d};;
let set_logic d s = {s with logic = d};;
let set_status d s = {s with status = d};;
let set_source d s = {s with source = d};;
let set_category d s = {s with category = d};;
let add_info d s = {s with info = s.info@[d]};;
let add_extrafuns d s = {s with extrafuns = d@s.extrafuns};;
let add_extrapreds d s = {s with extrapreds = d@s.extrapreds};;
let add_assumptions d s = {s with assumptions = d@s.assumptions};;
let add_formula d s = {s with formula = d};;

(*** FUNCTIONS ****************************************************************)
(*TODO: clean up*)
let top = Top;;
let bot = Bot;;
let rec add = function 
 | [] -> []
 | (Const n)::xs when n = Int64.zero -> add xs
 | x::xs -> x::add xs
;;

let rec mul = function 
 | [] -> []
 | (Const n)::xs when n = Int64.zero -> [Const n]
 | (Const n)::xs when n = Int64.one-> xs
 | x::xs -> x::mul xs
;;

let add xs = match add xs with
 | [] -> Const Int64.zero
 | [x] -> x
 | x::xs -> List.foldr (fun x y -> Add[x;y]) x xs
;;
let mul xs = match mul xs with
 | [] -> Const Int64.one
 | [x] -> x
 | x::xs -> List.foldr (fun x y -> Mul[x;y]) x xs
;;

let gt x y = if x = y then bot else Gt(x,y);;
let ge x y = if x = y then top else Ge(x,y);;
let eq x y = if x = y then top else Eq(x,y);;

(*TODO: clean up till here*)

(* printers *)
let p2f ppf t x = Format.fprintf ppf "%s" x;;
let va2f ppf x = p2f ppf "p" x;;
let vb2f ppf x = p2f ppf "a" x;;

let va2s x = va2f Format.str_formatter x; Format.flush_str_formatter ();;
let vb2s x = vb2f Format.str_formatter x; Format.flush_str_formatter ();;

let rec b2f ppf = function
 | Bot -> Format.fprintf ppf "false"
 | Top -> Format.fprintf ppf "true"
 | Varb v -> Format.fprintf ppf "%a" vb2f v
 | Not x -> Format.fprintf ppf "(not %a)" b2f x
 | Or ol -> Format.fprintf ppf "(or %a)" (List.fprintf b2f " ") ol
 | And ol -> Format.fprintf ppf "(and %a)" (List.fprintf b2f " ") ol
 | Iff ol -> Format.fprintf ppf "(iff %a)" (List.fprintf b2f " ") ol
 | Implies (x,y) -> Format.fprintf ppf "(implies %a %a)" b2f x b2f y
 | Eq (a,b) -> Format.fprintf ppf "(= %a %a)" a2f a a2f b
 | Ge (a,b) -> Format.fprintf ppf "(>= %a %a)" a2f a a2f b
 | Gt (a,b) -> Format.fprintf ppf "(> %a %a)" a2f a a2f b
 (* | Let (p,a,b) -> Format.fprintf ppf "(let %a %a %a)" va2f p a2f a b2f
 b *)
and a2f ppf = function
 | Const a -> Format.fprintf ppf "%s" (Int64.to_string a)
 | Vara v -> Format.fprintf ppf "%a" va2f v
 | Add al -> Format.fprintf ppf "(+ %a)" (List.fprintf a2f " ") al
 | Sub al -> Format.fprintf ppf "(- %a)" (List.fprintf a2f " ") al
 | Mul al -> Format.fprintf ppf "(* %a)" (List.fprintf a2f " ") al
 | Ite (p,a,b) -> Format.fprintf ppf "(ite %a %a %a)" b2f p a2f a a2f b
;;

let a_to_string a = 
 Format.fprintf Format.str_formatter "%a" a2f a;
 Format.flush_str_formatter ();
;;

let b_to_string b = 
 Format.fprintf Format.str_formatter "%a" b2f b;
 Format.flush_str_formatter ();
;;

let fprintf_a = a2f;;
let fprintf_b = b2f;;

(* print in STM-LIB like format *)
let fprintf_ef ppf (v,t) = Format.fprintf ppf "(%a %s)" va2f v t;;
let fprintf_ep ppf v = Format.fprintf ppf "(%a)" vb2f v;;
let fprintf_ass ppf b = Format.fprintf ppf ":assumption %a" fprintf_b b;;

let fprintf ppf ipt =
 let ef = ipt.extrafuns and ep = ipt.extrapreds in
 Format.fprintf ppf "@[(";
 Format.fprintf ppf "benchmark %s@\n" ipt.benchmark;
 Format.fprintf ppf ":logic %s@\n" ipt.logic;
 Format.fprintf ppf ":status %s@\n" ipt.status;
 if ef <> [] then Format.fprintf ppf ":extrafuns (%a)@\n"
  (List.fprintf fprintf_ef "@\n") ef;
 if ep <> [] then Format.fprintf ppf ":extrapreds (%a)@\n"
  (List.fprintf fprintf_ep "@\n") ep;
 Format.fprintf ppf "%a@\n" (List.fprintf fprintf_ass "@\n") ipt.assumptions;
 Format.fprintf ppf ":formula %a" fprintf_b ipt.formula;
 Format.fprintf ppf ")@]";
;;

(* substitutions *)
let rec sub_bb x phi f =
 let sf = sub_bb x phi in
 let sa = sub_ba x phi in
 if x = f then phi else match f with
  | Bot -> Bot
  | Top -> Top
  | Varb x -> Varb x
  | Not f -> Not (sf f)
  | Or xl -> Or (List.map sf xl)
  | And xl -> And (List.map sf xl)
  | Iff xl -> Iff (List.map sf xl)
  | Implies (x,y)-> Implies (sf x,sf y)
  | Eq (a,b) -> eq (sa a) (sa b)
  | Ge (a,b) -> ge (sa a) (sa b)
  | Gt (a,b) -> gt (sa a) (sa b)
  (*TODO: dangerous since x is not substituted*)
  (* | Let (x,a,b) -> Let (x,sa a, sf b) *)
and sub_ba x phi f = 
 let sb = sub_bb x phi in
 let sa = sub_ba x phi in
 match f with
 | Const a -> Const a
 | Vara v -> Vara v
 | Add al -> add (List.map sa al)
 | Sub al -> Sub (List.map sa al)
 | Mul al -> mul (List.map sa al)
 | Ite (p,a,b) -> Ite (sb p, sa a, sa b)
;;

let rec sub_aa x a f = 
 let sf = sub_aa x a in
 let sb = sub_ab x a in
 if x = f then a else match f with
  | Const a -> Const a
  | Vara v -> Vara v
  | Add al -> add (List.map sf al)
  | Sub al -> Sub (List.map sf al)
  | Mul al -> mul (List.map sf al)
  | Ite (p,a,b) -> Ite (sb p, sf a, sf b)
and sub_ab x a f =
 let sa = sub_aa x a in
 let sb = sub_ab x a in match f with
  | Bot -> Bot
  | Top -> Top
  | Varb x -> Varb x
  | Not f -> Not (sb f)
  | Or xl -> Or (List.map sb xl)
  | And xl -> And (List.map sb xl)
  | Iff xl -> Iff (List.map sb xl)
  | Implies (x,y) -> Implies (sb x,sb y)
  | Eq (a,b) -> eq (sa a) (sa b)
  | Ge (a,b) -> ge (sa a) (sa b)
  | Gt (a,b) -> gt (sa a) (sa b)
;;

let rec unfold_let = function
 | Const a -> Const a
 | Vara v -> Vara v
 | Add al -> Add (List.map unfold_let al)
 | Sub al -> Sub (List.map unfold_let al)
 | Mul al -> Mul (List.map unfold_let al)
 | Ite (x,a,b) -> Ite (unfold_b x, unfold_let a, unfold_let b)
and unfold_b = function
 | Bot -> Bot
 | Top -> Top
 | Varb x -> Varb x
 | Not f -> Not (unfold_b f)
 | Or xl -> Or (List.map unfold_b xl)
 | And xl -> And (List.map unfold_b xl)
 | Iff xl -> Iff (List.map unfold_b xl)
 | Implies (x,y) -> Implies (unfold_b x, unfold_b y)
 | Eq (a,b) -> Eq (unfold_let a, unfold_let b)
 | Ge (a,b) -> Ge (unfold_let a, unfold_let b)
 | Gt (a,b) -> Gt (unfold_let a, unfold_let b)
 (* | Let (x,a,b) -> sub_ab (Vara x) a (unfold_b b) *)
;;

let unfold ipt = 
 let ipt = {ipt with assumptions = List.map unfold_b ipt.assumptions} in
 let ipt = {ipt with formula = unfold_b ipt.formula} in
 ipt
;;

let rec count_a pa pb f = 
 let ca = count_a pa pb in
 let cb = count_b pa pb in
 match f with
  | Const a -> pa f 
  | Vara v -> pa f
  | Add al -> pa f + (List.foldr (fun a -> (+) (ca a)) 0 al)
  | Sub al -> pa f + (List.foldr (fun a -> (+) (ca a)) 0 al)
  | Mul al -> pa f + (List.foldr (fun a -> (+) (ca a)) 0 al)
  | Ite (x,a,b) -> pa f + cb x + ca a + ca b
and count_b pa pb f = 
 let ca = count_a pa pb in
 let cb = count_b pa pb in
 match f with
  | Bot -> pb f
  | Top -> pb f
  | Varb x -> pb f
  | Not x -> pb f + cb x
  | Or xl -> pb f + (List.foldr (fun a -> (+) (cb a)) 0 xl)
  | And xl -> pb f + (List.foldr (fun a -> (+) (cb a)) 0 xl) 
  | Iff xl -> pb f + (List.foldr (fun a -> (+) (cb a)) 0 xl)
  | Implies (x,y) -> pb f + cb x + cb y
  | Eq (a,b) -> pb f + ca a + ca b
  | Ge (a,b) -> pb f + ca a + ca b
  | Gt (a,b) -> pb f + ca a + ca b
  (* | Let(x,a,b) -> pb f + ca (Vara x) + ca a + cb b *)
;;

let count_add f = count_b (function Add _ -> 1 | _ -> 0) (fun _ -> 0) f;;
let count_sub f = count_b (function Sub _ -> 1 | _ -> 0) (fun _ -> 0) f;;
let count_mul f = count_b (function Mul _ -> 1 | _ -> 0) (fun _ -> 0) f;;
let count_var f = count_b (function Vara _ -> 1 | _ -> 0) (fun _ -> 0) f;;
let count_large_const f = count_b (function Const n when n >
Int64.of_int 100 -> 1 | _ -> 0) (fun _ -> 0) f;;

let count_sub ipt =
 List.foldr (fun f -> (+) (count_sub f)) (count_sub ipt.formula) ipt.assumptions
;;

(* top to bottom replacement of useless equalities *)
let rec unfold_eq = function
 | [] -> []
 | (Eq (Vara x, a) as f)::ass when count_var f < 10 -> 
  unfold_eq (List.map (sub_ab (Vara x) a) ass)
 | f::ass -> f::unfold_eq ass
;;

type context = {
 db   : int;
 ib   : int; (* bits used for arithmetic *)
 ob   : int;
 neg  : bool;
 rat  : int;
 real : bool;
 atbl : (var,Logic.a) H.t;
 atbl_rev : (Logic.a,var) H.t;
 btbl : (var,Logic.p) H.t;
 vdecl: (var*string) list;
};;

let ctx neg ib ob rat db real vdecl = {
 db    = db;
 ib    = ib;
 ob    = ob;
 neg   = neg;
 rat   = rat;
 real  = real;
 (*caching*)
 atbl  = H.create 512;
 atbl_rev  = H.create 512;
 btbl  = H.create 512;
 vdecl = vdecl;
};

module Statex = struct type t = context end;;
module M = Util.Monad.Transformer.State (Statex) (Logic.Monad);;

let (>>=) = M.(>>=);;

let default_spec =
 {L.min=Int64.zero; neg=false; rat=1; real=false; minf=false};;
let reset_spec = L.update_spec (fun _ -> default_spec);;

let cache_arith spec x = M.get >>= fun c -> 
 M.lift (L.(>>=) (L.cache_arith c.atbl spec x) (fun a ->
 H.replace c.atbl_rev (reset_spec a) x; L.return a));;
let cache_bool x = M.get >>= fun c -> 
 M.lift (L.cache_bool c.btbl x);;
let eval_a a ass = M.lift (Logic.eval_a a ass);;
let eval_p x ass = M.lift (Logic.eval_p x ass);;

(* TODO: check if bounds are tight *)
let lower x = function
 | Ge (Vara y, Const n) when x = y -> Some n
 | Gt (Vara y, Const n) when x = y -> Some (Int64.succ n)
 | Eq (Vara y, Const n) when x = y -> Some n
 | _ -> None
;;

let upper x = function
 | Ge (Const n, Vara y) when x = y -> Some n
 | Gt (Const n, Vara y) when x = y -> Some (Int64.pred n)
 | Eq (Const n, Vara y) when x = y -> Some n
 | Eq (Vara y, Const n) when x = y -> Some n
 | _ -> None
;;

let bounds_option neg x ass =
 let ls = List.map_option (lower x) ass in
 let us = List.map_option (upper x) ass in
 let ls = if neg then ls else Int64.zero::ls in
 ((if List.is_empty ls then None
   else Some (List.foldr min Int64.max_int ls)),
  (if List.is_empty us then None
   else Some (List.foldr max Int64.min_int us)))
;;

let lower mval x ls =
 let ls = List.map_option (lower x) ls in
 List.foldr max (Int64.neg (Int64.succ mval)) ls
;;

let upper mval x ls = 
 let ls = List.map_option (upper x) ls in
 List.foldr min mval ls
;;

let bounds neg ib ass x =
 let mval = Int64.bit_max_int ib in
 (*
 let lower = try lower x (List.find (is_lower x) ass) with Not_found -> -mval-1 in
 let upper = try upper x (List.find (is_upper x) ass) with Not_found -> mval in
 *)
 let lower = lower mval x ass in
 let upper = upper mval x ass in
 let neg = if (lower >= Int64.zero) then false else neg in
 (lower,upper,neg)
;;

let abs x = if x >= Int64.zero then x else Int64.neg x;;

let max_val neg ib ass x =
 if !infer then
  let l,u,n = bounds neg ib ass x in
  let mval = Pervasives.max (abs (Int64.succ l)) (abs u) in
  (mval,l,u,n)
 else
  let mval = Int64.bit_max_int ib in
  (mval,Int64.sub (Int64.neg mval) Int64.one,mval,neg)
 (*TODO: neg -> n?*)
;;

let spec ?(ass=[]) x : L.arith M.t = M.get >>= fun c -> 
 let mval,lower,upper,neg = max_val c.neg c.ib ass x in
 if ass <> [] then (
  Debug.debug (Format.sprintf "%s in [%s,%s], neg:%b" (va2s x) 
  (Int64.to_string lower) (Int64.to_string upper) neg);
 );
 M.return (
 match List.assoc x c.vdecl with
 | "Nat"  -> {L.min= mval;neg=false;rat=1;real=false;minf=false}
 | "Int"  -> {L.min= mval;neg=c.neg;rat=1;real=false;minf=false}
 | "Rat"  -> {L.min= mval;neg=c.neg;rat=c.rat;real=false;minf=false}
 | "Real" -> {L.min= mval;neg=c.neg;rat=c.rat;real=c.real;minf=false}
 )
;; 

let const_tf a = L.Number.of_64_int a;;

let foldl_aux f op al = 
 M.sequence (List.map f al) >>= fun al -> M.return (List.foldl1 op al);;

let tfb vdecl ipt = 
 let rec s2a = function
 | Const a -> M.return (L.constant (const_tf a))
 | Vara v -> M.get >>= fun c ->
   if H.mem c.atbl v then
    M.return (H.find c.atbl v)
   else
    spec ~ass:ipt.assumptions v >>= fun arith -> cache_arith arith v
 | Add al -> foldl_aux s2a (<+>) al 
 | Sub al -> foldl_aux s2a (<->) al 
 | Mul al -> foldl_aux s2a (<*>) al 
 | Ite (p,a,b) -> M.liftM3 L.ite (s2b p) (s2a a) (s2a b)
 and s2b = function
 | Bot -> M.return L.bot
 | Top -> M.return L.top
 | Varb v -> cache_bool v
 | Not x -> M.liftM L.neg (s2b x)
 | And xl -> foldl_aux s2b (<&>) xl
 | Or xl -> foldl_aux s2b (<|>) xl
 | Iff xl -> foldl_aux s2b (<<->>) xl
 | Implies (x,y) -> M.liftM2 (<->>) (s2b x) (s2b y)
 | Gt (a,b) -> M.liftM2 (<>>) (s2a a) (s2a b)
 | Ge (a,b) -> M.liftM2 (<>=>) (s2a a) (s2a b)
 | Eq (a,b) -> M.liftM2 (<=>) (s2a a) (s2a b)
in s2b (And (ipt.assumptions@[ipt.formula]));;

let get_assign ef ep assign = 
 M.map (fun (v,_) -> spec v >>= fun arith -> cache_arith arith v >>= fun a ->
  eval_a a assign >>= fun va ->
  M.return (v,va)) ef >>= fun al ->
 M.map (fun v -> cache_bool v >>= fun x ->
  eval_p x assign >>= fun vx ->
  M.return (v,vx)) ep >>= fun xl ->
 M.return (al,xl)
;;

let rec vara = function
 | Const _ -> []
 | Vara v -> [v]
 | Add al | Sub al | Mul al -> List.unique (List.flat_map vara al)
 | Ite (p,a,b) -> List.unique (vara_b p @ vara a @ vara b)
and vara_b = function
 | Bot | Top | Varb _ -> []
 | Not x -> vara_b x
 | Implies (x,y) -> List.unique (vara_b x @ vara_b y)
 | And ol | Or ol | Iff ol -> List.unique (List.flat_map vara_b ol)
 | Eq (a,b) | Ge (a,b) | Gt (a,b) -> List.unique (vara a @ vara b)
;;

let rec vars_inc_a is_mem_core = function
 | Const _ -> Some []
 | Vara a when is_mem_core a -> None
 | Vara _ -> Some []
 | Add _ | Sub _ | Mul _ | Ite _ as op
   when List.for_all (not <.> is_mem_core) (vara op) -> Some []
 | Add al | Sub al | Mul al ->
   let al' = List.map (vars_inc_a is_mem_core) al in
   if List.for_all Option.is_some al' then
    Some (List.concat (List.map_option id al'))
   else None
 | Ite (p,a,b) as ite ->
   let al' = List.map (vars_inc_a is_mem_core) [a;b] in
   if List.exists ((=) None) al' then Some (vara ite)
   else (match vars_inc_b is_mem_core p with
   | None -> Some (vara ite)
   | Some _ as p' -> Some (List.concat (List.map_option id (p'::al'))))
and vars_inc_b is_mem_core = function
 | Bot | Top | Varb _ -> Some []
 | Not x -> vars_inc_b is_mem_core x
 | Implies (x,y) ->
   let ol' = List.map (vars_inc_b is_mem_core) [x;y] in
   Some (List.concat (List.map_option id ol'))
 | And ol | Or ol | Iff ol ->
   let ol' = List.map (vars_inc_b is_mem_core) ol in
   Some (List.concat (List.map_option id ol'))
 | Eq (a,b) | Ge (a,b) | Gt (a,b) as rel ->
   let al' = List.map (vars_inc_a is_mem_core) [a;b] in
   if List.for_all Option.is_some al' then
    Some (List.concat (List.map_option id al'))
   else Some (vara_b rel)
;;

let solve' ctx ipt =
 Debug.debug "solve by bitblasting";
 Debug.debug (Format.sprintf "%d/%d arith/boolean vars" 
  (List.length ipt.extrafuns) (List.length ipt.extrapreds));
 L.run ~dbits:ctx.db ~obits:ctx.ob
 (M.run ctx (
 try tfb ipt.extrafuns ipt with | Failure "int_of_string" ->
  (Format.eprintf "integer conversion failed@\n%!"; M.return L.bot);
 >>= fun phi ->
 Debug.debug "SMT-LIB format resolved";
 (M.lift (Logic.solve2 ~solver:!solver phi)) >>= fun c ->
  match Logic.get_assignment c with
  | Some assign ->
    M.liftM Either.make_right (get_assign ipt.extrafuns ipt.extrapreds assign)
  | None ->
    M.return (Either.make_left (Logic.get_unsat_core c))
  ))
;;

let solve ib ob rat db real neg ipt =
 let rec solve ctx ipt =
    (* print core debugging information *)
    let inp_var = (H.find ctx.atbl_rev) <.> reset_spec in
    let fprintf_core debug_core = Debug.dprintf (fun ppf ->
     let fprintf_a ppf a = (if L.variables a <> [a] then L.fprintf_a ppf a
      else ((Format.fprintf ppf "%a" va2f) <.> inp_var) a) in
     Format.fprintf ppf "core: %t  " (debug_core fprintf_a)) in
  match solve' ctx ipt with
  | Left None -> UNKNOWN
  | Left Some (_, (* is_overflow_in_core *) true, debug_core) ->
    (* increase output bits *)
    let ob' = match !refine_ob with
    | AddB i -> ctx.ob + (Int64.to_int i)
    | MulB i -> ctx.ob * (Int64.to_int i) in
    Debug.debug ("Core contains variables from overflow constraints");
    Debug.debug (Format.sprintf "  increasing ob from %d to %d" ctx.ob ob');
    solve {ctx with ob = ob'} ipt
  | Left Some ([], _, debug_core) ->
    fprintf_core (fun fa -> debug_core ~fprintf_a:fa);
    UNKNOWN
  | Left Some (core, _, debug_core) ->
    fprintf_core (fun fa -> debug_core ~fprintf_a:fa);
    (* test for unsatisfiability *)
    let core_var = List.unique (List.flat_map L.variables core) in
    let core_var_a = List.map inp_var core_var in
    Debug.dprintf (fun ppf -> Format.fprintf ppf
     "core: %a" (List.fprintf L.fprintf_a ",") core);
    Debug.dprintf (fun ppf -> Format.fprintf ppf
     "variables in core: %a" (List.fprintf va2f ",") core_var_a);
    let unsat = List.for_all (fun (a,a') ->
     let spec = L.get_spec a in
     let s_l = if spec.L.neg then
      Int64.sub (Int64.neg spec.L.min) Int64.one else Int64.zero in
     let s_u = spec.L.min in
     let bounds = bounds_option spec.L.neg a' ipt.assumptions in
     let _ = Debug.dprintf (fun ppf ->
      Format.fprintf ppf "bounds for %a: %a" L.fprintf_a a
      (Pair.fprintf (Option.fprintf Int64.fprintf)
      (Option.fprintf Int64.fprintf)) bounds) in
     match bounds with
     | Some l, Some u -> l>=s_l && u<=s_u | _ -> false)
     (List.zip core_var core_var_a) in
    if unsat then UNSAT else (
    (* increase input bits *)
    let incr_min min =
     let op = match !(refine_ib) with
     | AddB i -> fun x -> Int64.mul x (Int64.pow (Int64.of_int 2) i)
     | MulB i -> fun x -> Int64.pow x i in
     let min' = Int64.pred (op (Int64.succ min)) in
     if min' < min then min else min' in
    let upd a spec =
     let min' = incr_min spec.L.min in
     Debug.debug (let _ = Format.fprintf Format.str_formatter "%a" va2f (inp_var a) in 
     let s = Format.flush_str_formatter () in
     Format.sprintf "Increasing domain for %s (%s to %s)"
      s (Int64.to_string spec.L.min) (Int64.to_string min'));
     {spec with L.min = min'} in
    (* determine which variables to increase according to Bryant *)
    let var_to_inc =
     let vars = Option.the <.> (vars_inc_b (flip List.mem core_var_a)) in
     List.unique <.> List.concat <.> (List.map vars) in
    let core' = var_to_inc (ipt.formula::ipt.assumptions) in
    Debug.dprintf (fun ppf -> Format.fprintf ppf
     "variables to increase: %a" (List.fprintf va2f ",") core');
    let changed = H.fold (fun s a changed ->
     if List.mem s core' then (
      let a' = L.update_spec (upd a) a in
      H.replace ctx.atbl s a';
      changed or (a <> a'))
     else changed) ctx.atbl false in
    if changed then solve ctx ipt else UNKNOWN)
  | Right assign -> SAT assign
 in
 solve (ctx neg ib ob rat db real ipt.extrafuns) ipt
;;


(* simplify *)

(* conjunctive form *)
let f2cf f = 
 let rec cf acc = function
  | And(xs) -> List.foldr (fun x acc -> cf acc x) acc xs
  | _x -> _x::acc
 in cf [] f
;;

let cf ipt = 
 let ipt = {ipt with assumptions = List.flat_map f2cf ipt.assumptions} in
 {ipt with formula = ipt.formula}
;;

(* additive form *)
let f2af f = 
 let rec af acc = function
  | Add(xs) -> List.foldr (fun x acc -> af acc x) acc xs
  | _x -> _x::acc
 in af [] f
;;

let af f = f2af f;;

(* multiplicative form *)
let f2mf f = 
 let rec mf acc = function
  | Mul(xs) -> List.foldr (fun x acc -> mf acc x) acc xs
  | _x -> _x::acc
 in mf [] f
;;

let mf f = f2mf f;;

let bound2 ipt x = 
 let decl = snd (List.find (fun v -> fst v = x) ipt.extrafuns) in
 (*TODO: replace*)
 let neg = decl <> "Nat" and ib = 2 in
 bounds neg ib ipt.assumptions x
;;

let tight_bounds ipt = 
 let bs = List.map (fun x -> (x,bound2 ipt (fst x))) ipt.extrafuns in
 let bs = List.filter (fun (_,(l,u,_)) -> l = u) bs in
 List.map (fun (x,(l,_,_)) -> 
 Debug.debug (Format.sprintf "bounds learned: %s = %s" (fst x) (Int64.to_string l));
 (Vara (fst x), Const l)) bs
;;
 
let val_var ipt = 
 let bs = List.map (fun (x,l) -> (Eq(x,l))) (tight_bounds ipt) in
 {ipt with assumptions = ipt.assumptions @ bs}
;;

(* substitute concrete values for variables *)
let sub_var ipt = 
 let tb = tight_bounds ipt in
 let sub tb f = List.foldr (fun (x,c) acc -> sub_ab x c acc) f tb in
 {ipt with assumptions = List.map (sub tb) ipt.assumptions}
;; 

let remove_x x xs ys = 
 if List.mem x xs && List.mem x ys 
  then List.remove x xs, List.remove x ys
  else xs,ys
;;

let remove xs ys = 
 let xs,ys = List.foldr (fun e (xs,ys) -> remove_x e xs ys) (xs,ys) xs in
 (add xs,add ys)
;;
 
let ca a b = remove (af a) (af b);;

let cancel_add = function
 | Gt(a,b) -> let a,b = remove (af a) (af b) in gt a b 
 | Ge(a,b) -> let a,b = remove (af a) (af b) in ge a b 
 | Eq(a,b) -> let a,b = remove (af a) (af b) in eq a b 
 | _x -> _x
;;

let cancel_add ipt = 
 {ipt with assumptions = List.map cancel_add ipt.assumptions}
;;

(*make pattern matching complete*)
(*TODO: Mul only sound for non-negative numbers!*)
let rec lower2 ipt = function
 | Vara a -> let (l,_,_) = bound2 ipt a in l
 | Add xs -> List.foldr (fun x -> Int64.add (lower2 ipt x)) Int64.zero xs
 | Mul xs when List.for_all (fun x -> lower2 ipt x >= Int64.zero) xs -> 
  List.foldr (fun x -> ( Int64.mul ) (lower2 ipt x)) Int64.one xs
 | Const n when n >= Int64.zero -> n
 | _ -> failwith "lower"
;;

let lower2 ipt f = try lower2 ipt f with Failure "lower" -> Int64.min_int

(*TODO: Mul only sound for non-negative numbers!*)
let rec upper2 ipt = function
 | Vara a -> let (_,u,_) = bound2 ipt a in u
 | Add xs -> List.foldr (fun x -> Int64.add (upper2 ipt x)) Int64.zero xs
 | Mul xs when List.for_all (fun x -> upper2 ipt x >= Int64.one) xs -> 
  List.foldr (fun x -> Int64.mul (upper2 ipt x)) Int64.one xs
 | Const n when n >= Int64.zero -> n
 | _ -> failwith "upper"
;;

let upper2 ipt f = try upper2 ipt f with Failure "upper" -> Int64.max_int

let learn_mul ipt = function 
 | Gt(Mul[a;b],c) -> 
  if lower2 ipt a >= Int64.zero && lower2 ipt b >= Int64.zero && lower2 ipt c >= Int64.zero
   then (
   let n0,n1 = Gt(a,Const Int64.zero), Gt(b,Const Int64.zero)  in
   Debug.debug (Format.sprintf "learn_mul: %s %s" (b_to_string n0) (b_to_string n1));
   [n0;n1]
   ) else []
 | Ge(Mul[a;b],c) -> 
  if lower2 ipt a >= Int64.zero && lower2 ipt b >= Int64.zero && lower2 ipt c > Int64.zero
   then [Gt(a,Const Int64.zero);Gt(b,Const Int64.zero)] else []
 | _x -> []
;;

let learn_mul ipt = 
 let bs = List.flat_map (learn_mul ipt) ipt.assumptions in
 {ipt with assumptions = ipt.assumptions @ bs}
;;

let unique ipt = 
 {ipt with assumptions = List.unique ipt.assumptions}
;;

(*
let sub_range x l u f = 
 List.map (fun a -> sub_ab x (Const a) f) (List.range l (u+1))
;;

(*do not instantiate if variable is not member*)
let instantiate ipt x =
 let (l,u,_) = bound2 ipt (fst x) in
 if l + 1 = u && l >= 0
  then 
   (*let _ = Format.printf "x(%s) = %s" (snd x) (fst x) in*)
   let x = Vara (fst x) in 
   {ipt with assumptions = List.flat_map (sub_range x l u) ipt.assumptions}
  else ipt
;;

(*find suitable variables to instantiate them*)
let instantiate ipt = List.foldl instantiate ipt ipt.extrafuns;;
*)

let simp_comp ipt = function
 | Ge(Mul[a;b],c) -> 
  if lower2 ipt a >= Int64.one && lower2 ipt b >= Int64.one && 
   (upper2 ipt c <= Int64.zero || a = c || b = c) 
  then top else Ge(Mul[a;b],c)
 | Ge(a,Mul[b;c]) when a = c && lower2 ipt a > Int64.zero -> Ge(Const(Int64.one),b)
 | _x -> _x
;;

let simp_comp ipt = 
 {ipt with assumptions = List.map (simp_comp ipt) ipt.assumptions}
;;

let learn_comp ipt = function
 | Gt(a,Add(xs)) when List.for_all (fun x -> lower2 ipt x >= Int64.zero) xs ->
  List.map (fun x -> Gt(a,x)) xs
 | _ -> []
;;

let learn_comp ipt = 
 let bs = List.flat_map (learn_comp ipt) ipt.assumptions in
 {ipt with assumptions = ipt.assumptions @ bs}
;;

(*TODO: extend to full power *)
let cancel_mul ipt = function
 | Gt(Mul[a;b],Mul[c;d]) when a = c && lower2 ipt a >= Int64.zero -> Gt(b,d)
 | Gt(Mul[a;b],Mul[c;d]) when a = d && lower2 ipt a >= Int64.zero -> Gt(b,c)
 | Gt(Mul[a;b],Mul[c;d]) when b = c && lower2 ipt b >= Int64.zero -> Gt(a,d)
 | Gt(Mul[a;b],Mul[c;d]) when b = d && lower2 ipt b >= Int64.zero -> Gt(a,c)
 | Ge(Mul[a;b],Mul[c;d]) when a = c && lower2 ipt a > Int64.zero -> Ge(b,d)
 | Ge(Mul[a;b],Mul[c;d]) when a = d && lower2 ipt a > Int64.zero -> Ge(b,c)
 | Ge(Mul[a;b],Mul[c;d]) when b = c && lower2 ipt b > Int64.zero -> Ge(a,d)
 | Ge(Mul[a;b],Mul[c;d]) when b = d && lower2 ipt b > Int64.zero -> Ge(a,c)
 | Ge(Const n,Mul[c;d]) when n = Int64.zero && lower2 ipt c > Int64.zero -> Eq(d,Const Int64.zero)
 | Ge(Const n,Mul[c;d]) when n = Int64.zero && lower2 ipt d > Int64.zero -> Eq(c,Const Int64.zero)
 | _x -> _x
;;

let cancel_mul ipt = 
 {ipt with assumptions = List.map (cancel_mul ipt) ipt.assumptions}
;;

let unsat ipt = function
 | Gt(a,b) ->
   List.intersect [Gt(b,a);Ge(b,a)] ipt.assumptions <> []
 | Eq(Mul[a;b],n) when n = Const Int64.zero ->
   lower2 ipt a > Int64.zero && lower2 ipt b > Int64.zero
 | _ -> false
;;

(*extend to non-zero values*)
let learn_nn ipt = function
 | Gt(Vara a,b) when lower2 ipt (Vara a) <= Int64.zero && lower2 ipt b = Int64.zero
  -> [Gt(Vara a,Const Int64.zero)]
 | Ge(Vara a,b) when lower2 ipt (Vara a) < Int64.zero && lower2 ipt b = Int64.zero
  -> [Ge(Vara a,Const Int64.zero)]
 | Eq(Vara a,b) when lower2 ipt (Vara a) < Int64.zero && lower2 ipt b = Int64.zero
  -> [Ge(Vara a,Const Int64.zero)]
 | _ -> []
;;

let learn_nn ipt = 
 let bs = List.flat_map (learn_nn ipt) ipt.assumptions in
 {ipt with assumptions = List.unique (ipt.assumptions @ bs)}
;;

let learn_nn ipt = fix learn_nn ipt;;

let unsat ipt = 
 if List.exists (unsat ipt) ipt.assumptions 
  then {ipt with assumptions = [bot]}
  else ipt
;;

let rec u2l = function
 | [] -> Top
 | (Eq(Vara x,a) as f)::xs when count_var f < 10 -> 
  sub_ab (Vara x) a (u2l xs)
 | f::xs -> And[f;(u2l xs)]
;;

let unfold_eq ipt = 
 let ipt = (cf ipt) in
 let bs = u2l ipt.assumptions in
 let ipt = {ipt with assumptions = [bs]} in
 let ipt = cf ipt in
 Debug.debug "unfold_eq finished";
 ipt
;;


(*side effects?*)
(*TODO: extend to ipt.formula and to disjunctions*)
let simplify ipt = 
 let ipt = {ipt with assumptions = ipt.assumptions@[ipt.formula]} in
 let ipt = {ipt with formula = Top} in
 let ipt = cf ipt in
 let ipt = val_var ipt in
 let ipt = sub_var ipt in
 let ipt = cancel_add ipt in
 let ipt = learn_mul ipt in
 let ipt = unique ipt in
 (*
 let ipt = instantiate ipt in
 *)
 let ipt = simp_comp ipt in
 let ipt = learn_comp ipt in
 let ipt = cancel_mul ipt in
 let ipt = unique ipt in
 let ipt = unsat ipt in
 ipt
;;

(* TEMP, generation of NLSOL input *)
type b2 = 
 | Bot2 | Or2 of b2 list | And2 of b2*b2 | Eq2 of a2*a2 | Ge2 of a2*a2 | Gt2 of a2*a2
and a2 =
 | Const2 of int | Vara2 of var
 | Add2 of a2*a2 | Mul2 of a2*a2
;;

let const2 x = Const2 (Int64.to_int x);;
let big_and2 ls = List.foldl (fun acc elt -> And2(acc,elt)) (List.hd ls) (List.tl ls)
let big_sum2 ls = List.foldl (fun acc elt -> Add2(acc,elt)) (List.hd ls) (List.tl ls)
let big_mul2 ls = List.foldl (fun acc elt -> Mul2(acc,elt)) (List.hd ls) (List.tl ls)

let rec tfb = function
 | Bot -> Bot2
 | Or(xl) -> Or2 (List.map tfb xl)
 | And(xl)-> big_and2 (List.map tfb xl)
 | Ge (a,b) -> Ge2(tfa a,tfa b)
 | Gt (a,b) -> Gt2(tfa a,tfa b)
 | _x -> Format.eprintf "%a unsupported@\n%!" fprintf_b _x; failwith "effi";
and tfa = function
 | Const a -> Const2 (Int64.to_int a)
 | Vara v -> Vara2 v
 | Add[a;b] -> Add2(tfa a,tfa b)
 | Mul[a;b] -> Mul2(tfa a,tfa b)
;;

let simpl f =
 let rec sb = function
  | Bot2 -> Bot2
  | And2(x,y) -> And2(sb x,sb y)
  | Or2(xl) -> Or2(List.map sb xl)
  | Gt2(x,y) -> Gt2(sa x,sa y)
  | Ge2(x,y) -> Ge2(sa x,sa y)
 and sa = function
  | Mul2(a,Add2(b,c))
  | Mul2(Add2(b,c),a) -> Add2(Mul2(sa a,sa b),Mul2(sa a,sa c))
  | Mul2(a,b) -> Mul2(sa a,sa b)
  | Add2(a,b) -> Add2(sa a,sa b)
  | _a -> _a
in sb f;;

let simp f = fix simpl f;;

let one_or_zero x =
 big_and2 [Eq2(Mul2(x,x),x); Ge2(x,const2 Int64.zero); Ge2(const2 Int64.one,x)]
;;

let rec max_or = function
 | Or2(ls) -> (List.flat_map max_or ls)
 | _a -> [_a]
;;

let rec max_and = function
 | And2(x,y) -> (List.flat_map max_and [x;y])
 | _a -> [_a]
;;

let rec b2f ppf = function
 | Bot2 -> Format.fprintf ppf "1 >= 0"
 | And2(x,y) -> Format.fprintf ppf "%a;@\n%a" b2f x b2f y
 | Or2(xs) -> Format.fprintf ppf "%a" (List.fprintf b2f " | ") xs
 | Eq2(a,b) -> Format.fprintf ppf "%a = %a" a2f a a2f b
 | Ge2(a,b) -> Format.fprintf ppf "%a >= %a" a2f a a2f b
 | Gt2(a,b) -> Format.fprintf ppf "%a > %a" a2f a a2f b
and a2f ppf = function
 | Const2 a -> Format.fprintf ppf "%d" (a)
 | Vara2 v -> Format.fprintf ppf "%a" va2f v
 | Add2(a,b) -> Format.fprintf ppf "%a + %a" a2f a a2f b
 | Mul2(a,b) -> Format.fprintf ppf "%a.%a" a2f a a2f b
;;

let rec nlsol f =
 let ts = H.create 512 in
 let fresh = ref 0 in
 let cache x = 
  if not (H.mem ts x) then (H.add ts x !fresh; incr fresh);
  Vara2 (Format.sprintf "aux_%d" (H.find ts x))
 in
 let rec resolve x = match x with 
  | And2(x,y) -> And2(resolve x, resolve y)
  | Gt2(p,q) as x -> let x = cache x in
  let c = Gt2(Add2(Mul2(x,p),Const2 1),Add2(Mul2(x,q),x)) in
  And2(one_or_zero x, simp c)
  | Ge2(p,q) as x -> let x = cache x in
  let c = Ge2(Mul2(x,p),Mul2(x,q)) in
  And2(one_or_zero x, simp c)
 in
 let alternative_mul x =
  big_mul2 (List.map cache (max_and x))
 in
 let alternative_add xs = 
 Ge2(big_sum2 (List.map alternative_mul xs),Const2 1)
 in
 let rec sb = function
  | Bot2 -> Ge2 (const2 Int64.zero, const2 Int64.one);
  | And2(x,y) -> And2(sb x, sb y)
  (*get maximal Ors out of it*)
  | Or2(xl) -> let cs = max_or (Or2(xl)) in
   big_and2 (alternative_add cs::List.map resolve cs)
  | _a -> _a
in sb f;;

let nlsol phi = nlsol (simp (tfb phi));;

let fprintf_nlsol ppf (b,l,s,ef,ep,ass,phi) =
 let phi = And(ass@[phi]) in 
 Format.fprintf ppf "%a" b2f (nlsol phi);
;;

let rec b2f ppf = function
 | Bot2 -> Format.fprintf ppf "false"
 | And2(x,y) -> Format.fprintf ppf "(and %a %a)" b2f x b2f y
 | Eq2(a,b) -> Format.fprintf ppf "(=  %a %a)" a2f a a2f b
 | Ge2(a,b) -> Format.fprintf ppf "(>= %a %a)" a2f a a2f b
 | Gt2(a,b) -> Format.fprintf ppf "(> %a %a)" a2f a a2f b
and a2f ppf = function
 | Const2 a -> Format.fprintf ppf "%d" (a)
 | Vara2 v -> Format.fprintf ppf "%a" va2f v
 | Add2(a,b) -> Format.fprintf ppf "(+ %a %a)" a2f a a2f b
 | Mul2(a,b) -> Format.fprintf ppf "(* %a %a)" a2f a a2f b
;;

let fprintf_b2 ppf x = b2f ppf (nlsol x);;

let fprintf_ef ppf (v,t) = Format.fprintf ppf "(%s %s)" v t;;
let fprintf_ep ppf v = Format.fprintf ppf "(%s)" v;;
let fprintf_ass ppf b = Format.fprintf ppf ":assumption %a" fprintf_b2 b;;

let fprintf_nlsol2 ppf ipt =
 let ef = ipt.extrafuns and ep = ipt.extrapreds in
 Format.fprintf ppf "(";
 Format.fprintf ppf "benchmark %s\n" ipt.benchmark;
 Format.fprintf ppf ":logic %s\n" ipt.logic;
 Format.fprintf ppf ":status %s\n" ipt.status;
 if ef <> [] then Format.fprintf ppf ":extrafuns (%a)\n"
  (List.fprintf fprintf_ef "@\n") ef;
 if ep <> [] then Format.fprintf ppf ":extrapreds (%a)\n"
  (List.fprintf fprintf_ep "\n") ep;
 Format.fprintf ppf "%a\n" (List.fprintf fprintf_ass "\n") ipt.assumptions;
 Format.fprintf ppf ":formula %a" fprintf_b2 ipt.formula;
 Format.fprintf ppf ")";
;;

(* verifying assignment for testing purposes *)
let check_ass ipt ((ass_a, ass_b) as ass) = 
 let foldl_aux f op xs = List.foldl1 op (List.map f xs) in
 let rec ev_a = function
  | Const a -> const_tf a
  | Vara v -> List.assoc v ass_a
  | Add al -> foldl_aux ev_a L.Number.add al
  | Sub al -> foldl_aux ev_a L.Number.sub al
  | Mul al -> foldl_aux ev_a L.Number.mul al
  | Ite (p,a,b) -> if ev_b p then ev_a a else ev_a b
 and ev_b = function
  | Bot -> false
  | Top -> true
  | Varb v -> List.assoc v ass_b
  | Not x -> not (ev_b x)
  | And xl -> foldl_aux ev_b (&&) xl
  | Or xl -> foldl_aux ev_b (||) xl
  | Iff xl -> foldl_aux ev_b (=) xl
  | Implies (x,y) -> not (ev_b x) || (ev_b y)
  | Gt (a,b) -> L.Number.gt (ev_a a) (ev_a b)
  | Ge (a,b) -> L.Number.ge (ev_a a) (ev_a b)
  | Eq (a,b) -> L.Number.eq (ev_a a) (ev_a b)
 in ev_b (And (ipt.assumptions@[ipt.formula]))
;;
