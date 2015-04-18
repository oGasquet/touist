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

(*** OPENS ********************************************************************)
open Util;;
open Rewritingx;;
open Logic.Operators;;

(*** MODULES ******************************************************************)
module AF = Filtering;;
module C = Coefficient;;
module Co = Complexity;;
module F = Format;;
module Fun = Function;;
module H = Hashtbl;;
module M = Rewritingx.Monad;;
module Number = Logic.Number;;
module Pos = Position;;
module Prec = Precedence;;
module Sig = Signature;;
module Var = Variable;;
module WF = Weights;;
module Mono = Monomial.Make (C) (Var);;
module P = Polynomial.Make (Mono);;

module NM = Matrix.Make (Number);;
module Intp = Interpretation.Make (NM);;
module XO = XmlOutput;;


(*** TYPES ********************************************************************)
type goal = Prec | Weight;;

type context = {
 arith                 : Logic.arith;
 w0                    : Logic.a ref;
 solver                : Logic.solver;
 prec_num              : int;
 af_l                  : (Fun.t, Logic.p) H.t;
 af_p                  : (Fun.t * int, Logic.p) H.t;
 usable                : (Fun.t, Logic.p) H.t;
 (* weights               : (Fun.t, Logic.a) H.t; *)
 precs                 : (Fun.t, Logic.a) H.t;
 state                 : Signature.t;
 gt_encodings          : (Rule.t, Logic.p) H.t;
 eq_af_encodings       : (Fun.t*Fun.t*Term.t list*Term.t list, Logic.p) H.t;
 emb_gt_encodings      : (Rule.t, Logic.p) H.t;
 emb_eq_encodings      : (Rule.t, Logic.p) H.t;
 kbo_af_same_encodings : (Fun.t*Term.t list*Term.t list,Logic.p) H.t;
 kbo_af_diff_encodings : (Fun.t*Fun.t*Term.t list*Term.t list,Logic.p) H.t;
 pbc_gt                : (Fun.t*Fun.t, Logic.a) H.t;
 pbc_eq                : (Fun.t*Fun.t, Logic.a) H.t;
 pbc_no                : (Fun.t*Fun.t, Logic.a) H.t;
 pbc_kbo               : (Term.t*Term.t, Logic.a) H.t;
 pbc_kbo2              : (Term.t*Term.t, Logic.a) H.t;
 goal                  : goal option;
 subterm_encodings     : (Term.t,P.t) Hashtbl.t;
 coefficients          : (Fun.t*int,C.t) Hashtbl.t;
 subterm_encodings2    : (Term.t,Logic.a list) Hashtbl.t;
 coefficients2         : (Fun.t,Logic.a list) Hashtbl.t;
 constants             : (Fun.t,C.t) Hashtbl.t;
 p_gt_encodings        : (Rule.t,Logic.p) Hashtbl.t;
 p_geq_encodings       : (Rule.t,Logic.p) Hashtbl.t;
};;

type flags = {
 dp : bool ref;
 deg : int ref;
 dir : bool ref;
 ep : bool ref;
 help : bool ref;
 min : int ref;
 smin : int ref;
 minp : bool ref;
 minw : bool ref;
 ob : int ref;
 pbc : bool ref;
 quasi : bool ref;
 rat : int ref;
 sat : bool ref;
 ur : bool ref;
};;

type t = {
 af : AF.t option;
 input : Problem.t;
 output : Problem.t;
 precedence : Prec.t;
 usable_rules : Trs.t option;
 intp : (Intp.t,(string * Number.t list) list) either;
};;

(*** GLOBALS ******************************************************************)
let code = "tkbo";;
let name = "TKBO Processor";;
let comment = "Applies transfinite Knuth-Bendix order."
let keywords = ["transfinite knuth-bendix order";"simplification order";"termination"];;

let flags = {
 dp = ref false;
 deg = ref 0;
 dir = ref false;
 ep = ref false;
 help = ref false;
 min = ref 3;
 smin = ref ~-1;
 minp = ref false;
 minw = ref false;
 ob = ref max_int;
 pbc = ref false;
 quasi = ref false;
 rat = ref 1;
 sat = ref true;
 ur = ref false;
};;

let spec =
 let spec = [
  ("-af",Arg.Set flags.dp,
   "Allows non-monotone interpretations (argument filterings). This flag \
    cannot be used in combination with `-pbc'.");
  ("-dp",Arg.Set flags.dp,
   "Equivalent to `-af'.");
  ("-degree",Arg.Set_int flags.deg, "degree of ordinal interpretation (default 0)");
  ("-direct",Arg.Set flags.dir, "direct proof (orient all rules in one go)");
  ("-ep",Arg.Set flags.ep,"Demands an empty precedence (only for `-pbc').");
  ("--help",Arg.Set flags.help,"Prints information about flags.");
  ("-help",Arg.Set flags.help,"Prints information about flags.");
  ("-h",Arg.Set flags.help,"Prints information about flags.");
  ("-ib",Arg.Int ((:=) flags.min <.> Int.bit_max),
   "Defines the number of bits used to represent weigths (same as \
   `-min' but in bits).");
  ("-max",Arg.Int ((:=) flags.ob <.> Int.bits),
   "Defines the maximum number that can appear as intermediate result.");
  ("-min",Arg.Set_int flags.min,
   "Defines the minimum weight that should be representable (default 3.");
  ("-smin",Arg.Set_int flags.smin,
   "Defines the minimum subterm coefficient that should be representable
   (default same as -min).");
  ("-minp",Arg.Set flags.minp,
   "Minimizes the precedence comparisons (only for `-pbc').");
  (* ("-minw",Arg.Set flags.minw, *)
   (* "Minimize the sum of weights (only for `-pbc')."); *)
  ("-ob",Arg.Set_int flags.ob,
   "Defines the number of bits used to represent intermediate results
    (same as `-max' but in bits)");
  ("-sb",Arg.Int ((:=) flags.smin <.> Int.bit_max),
   "Defines the number of bits used to represent subterm coefficients");
  ("-pbc",Arg.Set flags.pbc,"Uses PBC backend.");
  ("-quasi",Arg.Set flags.quasi,"Allows quasi-precedences.");
  ("-rat",Arg.Set_int flags.rat,
   "Sets the denumerator (only in combination with `-sat' or `-smt').");
  ("-sat",Arg.Set flags.sat,"Uses SAT backend (default).");
  ("-smt",Arg.Clear flags.sat,"Uses SMT backend.");
  ("-ur",Arg.Set flags.ur,
   "Uses usable rules with respect to argument filtering.")]
 in
 let a = Arg.alignx 80 spec in
 a
;;

let help = (comment,keywords,List.map Triple.drop_snd spec);;

(*** MODULES (part 2) *********************************************************)
module Statex = struct type t = context end;;
module Made = Util.Monad.Transformer.State (Statex) (Logic.Monad);;
open Made;;

(*** FUNCTIONS ****************************************************************)
let init _ =
 flags.dp := false;
 flags.deg := 0;
 flags.dir := false;
 flags.ep := false;
 flags.help := false;
 flags.min := 1;
 flags.minp := false;
 flags.minw := false;
 flags.ob := max_int;
 flags.pbc := false;
 flags.quasi := false;
 flags.rat := 1;
 flags.sat := true;
 flags.ur := false;
;;

(* Constructors and Destructors *)
let make af input output precedence ur intp = {
 af = af;
 input = input;
 output = output;
 precedence = precedence;
 usable_rules = ur;
 intp = intp;
};;

let get_ip p = p.input;;
let get_op p = p.output;;

(* Complexity Bounds *)
let complexity c _ = Co.mul c Co.other;;

(* Compare Functions *)
let equal p q =
 Problem.equal p.input q.input && Problem.equal p.output q.output
;;

(* Printers *)
let (>>=) = M.(>>=);;

let fprintf_af fmt = function
 | None -> Monad.return ()
 | Some af ->
  F.fprintf fmt "@\n@[<1>argument filtering:@\n";
  AF.fprintfm fmt af >>= fun _ -> Monad.return (F.fprintf fmt "@]")
;;

let fprintf_ur fmt = function
 | None -> Monad.return ()
 | Some trs ->
  F.fprintf fmt "@\n@[<1>usable rules:@\n";
  Trs.fprintfm fmt trs >>= fun _ -> Monad.return (F.fprintf fmt "@]")
;;


let fprintf_elt i fmt c =
 if i = 0 then Number.fprintf fmt c
 else Format.fprintf fmt "w^%d %a" i Number.fprintf c
;;

let fprintf_intp_p fmt (f,c::cs) = 
 F.fprintf fmt "%s(x) =  x %a+ " f Number.fprintf c;
 let n = List.length cs -1 in
 List.fprintfi (fun i c -> fprintf_elt (n-i) c) " + " fmt cs
;;

let fprintf_intp2 fmt intp = List.fprintf fprintf_intp_p "@\n" fmt intp;;

let fprintf_intp fmt = function
 | Left intp -> Intp.fprintf fmt intp
 | Right intp -> 
 fprintf_intp2 fmt intp; Monad.return ();
;;

let fprintf fs fmt p  = 
 F.fprintf fmt "@[<1>%s:" name;
 fprintf_af fmt p.af >>= fun _ ->
 fprintf_ur fmt p.usable_rules >>= fun _ ->
 F.fprintf fmt "@\n@[<1>transfinite weight function:@\n";
 (* Intp.fprintf fmt p.intp >>= fun _ -> *)
 fprintf_intp fmt p.intp >>= fun _ ->
 F.fprintf fmt "@]@\n@[<1>precedence:@\n";
 Prec.fprintfm fmt p.precedence >>= fun _ ->
 F.fprintf fmt "@]@\n@[<1>problem:@\n";
 Problem.fprintfm fmt p.output >>= fun _ ->
 F.fprintf fmt "@]@\n"; List.hd fs fmt >>= fun _ ->
 Monad.return (F.fprintf fmt "@]")
;;

let fprintfx_af = function
  | None    -> XO.id
  | Some af -> AF.fprintfx af
;;

let fprintfx_wf_p wf p = XO.node "precedenceWeight" (List.map (fun (f, p) ->
  let (scfs,w) = Intp.get wf f in
  let w_to_num = (fun w -> Number.to_int (NM.get 0 0 w)) in
  XO.node "precedenceWeightEntry" [
    M.fprintfx_fun f;
    (fun fmt -> M.find_ari f >>= fun a -> XO.int "arity" a fmt);
    XO.int "precedence" p;
    XO.int "weight" (w_to_num w);
    XO.node "subtermCoefficientEntries" (List.map (fun scf ->
       XO.int "entry" (w_to_num scf)) scfs)
    ]
  ) p);;

let fprintfx_redpair p = XO.node "orderingConstraintProof" [XO.node "redPair" [
  XO.node "knuthBendixOrder" [
    XO.int "w0" 1; (* currently, the interpretation is fixed to 1 *)
    (match p.intp with 
      | Left intp -> fprintfx_wf_p intp (Prec.to_list p.precedence) 
      | Right _ -> failwith "Tbko.fprintfx: Ordinal interpretations unsupported"
    );
    fprintfx_af p.af
  ]
]];;

let fprintfx_ur = function
  | Some ur -> XO.node "usableRules" [Trs.fprintfx ur]
  | None    -> XO.id
;;

let fprintfx fs p =
  let dp = Problem.is_dp p.input in
  if dp || Problem.is_rp p.input || Problem.is_sp p.input then (
    let tag = if dp then "redPairProc" else "ruleRemoval" in
    XO.node tag [
      fprintfx_redpair p;
      Problem.fprintfx p.output;
      fprintfx_ur p.usable_rules;
      List.hd fs
    ]
  ) else (
    failwith "Tkbo.fprintfx: XML output not supported"
  )
;;


(* general functions *)
let (>>=) = Made.(>>=);;

let rec symbols_list = function 
 | Term.Var _ -> []
 | Term.Fun (f,ts) -> f::List.flat_map symbols_list ts;;

let rec vars_list = function 
 | Term.Var x -> [x]
 | Term.Fun (_,ts) -> List.flat_map vars_list ts;;

let diff a b = List.foldr List.remove a b;;

(* functions lifted from Logic into Made *)
let fresh_arith_spec spec = lift (Logic.fresh_arith spec);;
let fresh_arith = get >>= fun s -> lift (Logic.fresh_arith s.arith);;
let fresh_bool = get >>= fun s -> lift Logic.fresh_bool;;

let eval_a a ass = a >>= fun a -> lift (Logic.eval_a a ass);;
let eval_p p ass = p >>= fun p -> lift (Logic.eval_p p ass);;

let ($>=$) a b = liftM2 (<>=>) a b;;
let ($=$) a b = liftM2 (<=>) a b;;
let ($>$) a b = liftM2 (<>>) a b;;
let ($->$) a b = liftM2 (<->>) a b;;
let ($|$) a b = liftM2 (<|>) a b;;
let ($&$) a b = liftM2 (<&>) a b;;
let ($*$) a b = liftM2 (<*>) a b;;
let ($+$) a b = liftM2 (<+>) a b;;
let ($-$) a b = liftM2 (<->) a b;;

let map_op op f ls = sequence (List.map f ls) >>= (return <.> op);;
let mapi_op op f ls = sequence (List.mapi f ls) >>= (return <.> op);;
let gen_op op f n = sequence (List.gen f n) >>= (return <.> op);;
let map_and f = map_op Logic.big_and f;;
let mapi_and f = mapi_op Logic.big_and f;;
let gen_and f = gen_op Logic.big_and f;;
let map_or f = map_op Logic.big_or f;;
let mapi_or f = mapi_op Logic.big_or f;;
let gen_or f = gen_op Logic.big_or f;;

(* actual content starts here *)
let context state fs =
 let arith = {
  Logic.min = Int64.of_int !(flags.min);
  neg = false;
  rat = !(flags.rat);
  real = false;
  minf = false}
 in
 let solver =
  if !(flags.sat) then Logic.MiniSat else
  if !(flags.pbc) then Logic.MiniSatP else Logic.Yices
 in
 let goal =
  if !(flags.minp) then Some Prec else
  if !(flags.minw) then Some Weight else None
 in
 {
  arith             = arith; 
  w0                = ref Logic.one;
  solver            = solver;
  prec_num          = max 0 (List.length fs - 1);
  af_l              = H.create 512;
  af_p              = H.create 512;
  usable            = H.create 512;
  (* weights           = H.create 512; *)
  precs             = H.create 512;
  state             = state;
  eq_af_encodings   = H.create 512;
  gt_encodings      = H.create 512;
  emb_gt_encodings  = H.create 512;
  emb_eq_encodings  = H.create 512;
  kbo_af_same_encodings = H.create 512;
  kbo_af_diff_encodings = H.create 512;
  pbc_gt            = H.create 512; 
  pbc_eq            = H.create 512; 
  pbc_no            = H.create 512; 
  pbc_kbo           = H.create 512; 
  pbc_kbo2          = H.create 512; 
  goal              = goal;
  subterm_encodings = H.create 512;
  coefficients      = H.create 512;
  subterm_encodings2= H.create 512;
  coefficients2     = H.create 512;
  constants         = H.create 512;
  p_gt_encodings      = H.create 512;
  p_geq_encodings     = H.create 512;
 }
;;

(* administrative functions *)
let cache_m tbl f k = 
 if H.mem tbl k then return (H.find tbl k)
 else (f k >>= fun v -> (H.add tbl k v; return v))
;;

(* Ordinals begin *)
let degree () = 
 return !(flags.deg)
;;

let subterm_coefficient arith = 
 if !(flags.smin) = 1 then return Logic.one
 else
  let arith = {arith with Logic.min = Int64.of_int !(flags.smin)} in
  fresh_arith_spec arith
;;

let make_coefficient f = get >>= fun c -> 
 degree () >>= fun d ->
 subterm_coefficient c.arith >>= fun sc -> 
 Made.sequence (return sc::List.gen (fun _ -> fresh_arith) (d+1))
;;

let coefficients2 f = get >>= fun c ->
 cache_m c.coefficients2 make_coefficient f
;;

let rec add acc p0 p1 = match p0,p1 with
 | [],[] -> []
 | c0::p0,c1::p1 -> 
  let acc' = acc <&> (c1 <=> Logic.zero) in
  ((Logic.ite acc c0 Logic.zero) <+> c1)::add acc' p0 p1
;;

let add p0 p1 = add Logic.top p0 p1;;

let rec encode_term t = get >>= fun c ->
 cache_m c.subterm_encodings2 (etc c) t
and etc c = function
 | Term.Var x -> 
  degree () >>= fun d ->
  return (Logic.one::List.replicate (d+1) Logic.zero)
 | Term.Fun (f, [t]) ->
   encode_term t >>= fun es ->
   coefficients2 f >>= fun (f'::fs) ->
   let e'::es' = List.map ((<*>) f') es in
   return (e'::add es' fs)
;;

(* for the "ordinal" coefficients *)
let rec greater_equal_poly p0 p1 = match p0,p1 with
 | [],[] -> Logic.top
 | c0::p0, c1::p1 -> c0 <>> c1 <|> (c0 <>=> c1 <&> greater_equal_poly p0 p1)
;;

let rec greater_poly p0 p1 = match p0,p1 with
 | [],[] -> Logic.bot
 | c0::p0, c1::p1 -> c0 <>> c1 <|> (c0 <=> c1 <&> greater_poly p0 p1)
;;

(* for the "variable" coefficient *)
let greater_equal_poly p0 p1 = match p0,p1 with
 | c0::p0, c1::p1 -> c0 <>=> c1 <&> greater_equal_poly p0 p1
;;
let greater_poly p0 p1 = match p0,p1 with
 | c0::p0, c1::p1 -> c0 <>=> c1 <&> greater_poly p0 p1
;;

let ogreater_equal_rule rule = get >>= fun c ->
 liftM2 (greater_equal_poly) (encode_term (Rule.lhs rule))
  (encode_term (Rule.rhs rule))
;;

let ogreater_rule rule = get >>= fun c ->
 liftM2 (greater_poly) (encode_term (Rule.lhs rule))
  (encode_term (Rule.rhs rule))
;;

(* ordinals end *)

(* KBO encoding starts here *)
let make_coefficient f _ = get >>= fun c -> subterm_coefficient c.arith;;

let make_constant f = get >>= fun c -> fresh_arith_spec c.arith;;

let coefficient f i = get >>= fun c -> 
 cache_m c.coefficients (uncurry make_coefficient) (f,i)
;;

let constant f = get >>= fun c -> cache_m c.constants make_constant f;;

(* let weight f = get >>= fun c -> cache_m c.weights (const fresh_arith)
f;; *)

let prec f = get >>= fun c -> 
 let arith = Logic.nat c.prec_num in
 cache_m c.precs (const (fresh_arith_spec arith)) f
;;

let prec_gt f g = prec f $>$ prec g;;
let prec_ge f g = prec f $>=$ prec g;;

let u t =
 get >>= fun c ->
 cache_m c.usable (const fresh_bool) (Option.the(Term.root t))
;;

let af_l f = get >>= fun c -> cache_m c.af_l (const fresh_bool) f;;
let af_n f = af_l f >>= (return <.> Logic.neg);;
let af_p f i = get >>= fun c -> cache_m c.af_p (const fresh_bool) (f,i);;

(* unary(u) \land w(u) = 0 \to u maximal element *)
let max u fs = get >>= fun c ->
 if !(flags.quasi) then map_and (prec_ge u) fs 
 else map_and (fun f -> if f = u then return Logic.top else prec_gt u f) fs
;;

let arity f = get >>= fun c -> return (Sig.find_ari f c.state);;
let get_name f = get >>= fun c -> return (Sig.find_fun_name f c.state);;
let n_ary n fs = Made.filter (fun f -> liftM2 (=) (arity f) (return n)) fs;;
let w0 = get >>= fun c -> return !(c.w0);;

let adm fs = get >>= fun c -> 
 let adm_c fs = n_ary 0 fs >>= fun cs ->
  map_and (fun con -> constant con $>$ return C.zero) cs
 in
 let adm_u fs = n_ary 1 fs >>= fun us ->
  map_and (fun u -> (constant u $=$ return C.zero) $->$ (max u fs)) us
 in
 adm_c fs $&$ adm_u fs
;;


let rec encode_term t = get >>= fun c ->
 cache_m c.subterm_encodings (etc c) t
and etc c = function
 | Term.Var x -> return (P.make [Mono.make C.one [x]; Mono.make C.zero []])
 | Term.Fun (f, ts) ->
  (List.fold_lefti (fun i p t -> 
   liftM2 P.add p (liftM2 P.scale (coefficient f i) (encode_term t)))
  (liftM P.make (sequence [liftM2 Mono.make (constant f) (return [])]))
  ts)
;;

let greater_mono m0 m1 = C.gt (Mono.coefficient m0) (Mono.coefficient m1);;
let greater_equal_mono m0 m1 = C.geq (Mono.coefficient m0) (Mono.coefficient m1);;

let greater_equal_poly p0 p1 =
 let (v0,v1) = Pair.map P.variables (p0,p1) in
 if not (List.is_subset v1 v0) then 
   Logic.bot
 else
  let p0 = P.filter (fun m -> List.mem (Mono.variables m) v1) p0 in
  let cs = P.map2 greater_equal_mono p0 p1 in 
  Logic.big_and cs 
;; 

(*TODO HZ: improve comparison by (taking w_0 into account)*)
let greater_poly p0 p1 = 
 let c0 = P.constant_part p0 in
 let c1 = try P.constant_part p1 with Not_found -> 
  let m = Mono.coefficient c0 in
  Mono.make C.zero []
 in
 let (nc0, nc1) = Pair.map P.non_constant_part (p0,p1) in
 greater_mono c0 c1 <&> greater_equal_poly nc0 nc1
;;

let greater_equal_rule rule = 
 liftM2 greater_equal_poly (encode_term (Rule.lhs rule))
  (encode_term (Rule.rhs rule))
;;

let greater_equal_rule_s rule = 
 let ncp = P.non_constant_part in
 encode_term (Rule.lhs rule) >>= fun l ->
 encode_term (Rule.rhs rule) >>= fun r ->
 return (greater_equal_poly (ncp l) (ncp r)) 
;;

let greater_equal_rule rule = get >>= fun c ->
 cache_m c.p_geq_encodings greater_equal_rule rule
;;

let greater_rule rule =
 liftM2 greater_poly (encode_term (Rule.lhs rule))
  (encode_term (Rule.rhs rule))
;;

let greater_rule rule = get >>= fun c ->
 cache_m c.p_gt_encodings greater_rule rule
 (* greater_rule rule *)
;;

let mon_m m = return (C.geq m C.one);;

let coefficients f = arity f >>= fun a ->
 Made.sequence (List.gen (coefficient f) a)
;;

let matrices fs = Made.flat_map coefficients fs;;

let mon fs = matrices fs >>= fun ms -> map_and mon_m ms;;

let rec kbo_gt rule =
 let helper rule = 
  if (not (Rule.is_rewrite_rule rule)) || Rule.is_embedded (Rule.invert rule) then
   return Logic.bot
  else if Rule.is_proper_embedded rule then
   return Logic.top
  else (
   degree () >>= fun d ->
   let gt = if d = 0 then greater_rule else ogreater_rule in
   let ge = if d = 0 then greater_equal_rule else ogreater_equal_rule in
   gt rule >>= fun w1 ->
   ge rule >>= fun w2 -> 
   match Rule.to_terms rule with
    | Term.Var _, _ -> return Logic.bot 
    | Term.Fun _, Term.Var _ -> return Logic.top
     (* all dangerous cases are considered above*)
    | Term.Fun (f0, ts0), Term.Fun (f1, ts1) -> get >>= fun c ->
     (if f0 = f1 then begin
      let ts0', ts1' = List.remove_equal ts0 ts1 in
      if (ts0' = [] || ts1' = []) then return Logic.bot
      else kbo_gt (Rule.of_terms (List.hd ts0') (List.hd ts1'))
     end
     else begin (* different function symbols *)
      (if !(flags.quasi) then 
      let ts0', ts1' = List.remove_equal ts0 ts1 in
      (if ts0' = [] || ts1' = [] then return Logic.bot
       else kbo_gt (Rule.of_terms (List.hd ts0') (List.hd ts1'))) >>= fun aux ->
       prec_gt f0 f1 $|$ (prec_ge f0 f1 $&$ return aux)
      else prec_gt f0 f1) end) >>= fun aux ->
  return (w1 <|> (w2 <&> aux))
  ) in
  get >>= fun c -> cache_m c.gt_encodings helper rule
;;

let kbo_ge rule =
 if Rule.uncurry (=) rule then return Logic.top else kbo_gt rule
;;

(*dummies*)
let encode_gt = if !(flags.dir) then map_and kbo_gt else map_or kbo_gt;;
let encode_ge s w = map_and kbo_ge (s@w)
let af _ = return Logic.top

let subterm_f f = coefficients2 f >>= fun (f'::fs) ->
 return (f' <>> Logic.zero) $&$ map_or (fun c -> return (c <>> Logic.zero)) fs
;;

let subterm fs = map_and subterm_f fs;;

let encode s w = get >>= fun c ->
 fresh_arith >>= fun w0 -> c.w0 := w0;
 let fs = (Trs.funs (Trs.union s w)) in
 let s, w = Pair.map Trs.to_list (s, w) in
 degree () >>= fun d ->
 encode_gt s $&$
 encode_ge s w $&$
 adm fs $&$
 af fs $&$
 mon fs $&$
 (if d = 0 then return Logic.top else subterm fs) $&$
 return Logic.top
;;

(* decode from assignment *)
let decode_rule ass rule = get >>= fun c ->
  liftM not (eval_p (kbo_gt rule) ass)
;;

let decode_trs ass trs = 
 Made.filter (decode_rule ass) (Trs.to_list trs) >>= (return <.> Trs.of_list)
;;

let decode ass s w = get >>= fun c -> 
 liftM2 Pair.make
  (decode_trs ass s) (if !(flags.dp) then return w else decode_trs ass w)
;;

let decode_ur_rule ass rule = eval_p (u (Rule.lhs rule)) ass;;

let decode_trs_ur ass w =
 liftM Trs.of_list (Made.filter (decode_ur_rule ass) (Trs.to_list w))
;;

let decode_ur ass w = get >>= fun c ->
 if !(flags.ur) then (decode_trs_ur ass w >>= (return <.> Option.some))
 else (return None)
;;

let eval_matrix ass m = m >>= fun m -> 
 lift (Logic.eval_a m ass) >>= fun c ->
 return (NM.make 1 1 c)
;;

let get_interpretation ass f = arity f >>= fun a ->
 Made.sequence 
  (List.gen (fun i -> eval_matrix ass (coefficient f i)) a) >>= fun coeffs ->
 eval_matrix ass (constant f) >>= fun const ->
 return (f, coeffs, const);;

let decode_intp ass trs = 
 Made.sequence (List.map (get_interpretation ass) (Trs.funs trs)) >>=
  (return <.> List.foldr (fun fi acc -> uncurry3 (Intp.add acc) fi)
   (Intp.empty ()))
;;


let get_interpretation2 ass f = get_name f >>= fun name ->
 coefficients2 f >>= fun fs ->
 Made.sequence (List.map (fun f -> eval_a (return f) ass) fs) >>= fun cs ->
 return (name,cs)
;;

let decode_intp2 ass trs = 
 Made.sequence (List.map (get_interpretation2 ass) (Trs.funs trs))
;;

let decode_intp ass trs = 
 degree () >>= fun d ->
 if d = 0 then 
  decode_intp ass trs >>= fun i ->
  return (Left i)
 else
  decode_intp2 ass trs >>= fun i ->
  return (Right i)
;;

let decode_prec_f ass f =
 eval_a (prec f) ass >>= fun p -> 
 return (f,int_of_string (Number.to_string p))
;;

let decode_prec ass s w =
 let fs = Trs.funs (Trs.union s w) in
 Made.sequence (List.map (decode_prec_f ass) fs) >>= fun ps ->
 return (Prec.of_list ps)
;;

let decode_af_f ass f =
 arity f >>= fun a ->
 sequence (List.gen (fun i -> eval_p (af_p f i) ass) a) >>= fun ps -> 
 let psi = List.mapi Pair.make ps in
 let ps = List.filter snd psi in
 let ps = List.map fst ps in
 eval_p (af_l f) ass >>= fun l ->
 if l then return (f,AF.List ps)
 else (assert (List.length ps = 1); return (f,AF.Collapsing (List.hd ps)))
;;

let decode_af ass s w = get >>= fun c ->
 if !(flags.dp) then (
 let fs = Trs.funs (Trs.union s w) in
 Made.sequence (List.map (decode_af_f ass) fs) >>= fun af ->
 return (Some (AF.of_list af))
 ) else return None
;;


let solve signature fs p = 
 let configure s = F.printf "%s@\n%!" s; flags.help := true in
 (try init (); Arg.parsex code spec fs with Arg.Bad s -> configure s);
 if !(flags.help) then (Arg.usage spec ("Options for "^code^":"); exit 0);
 if !(flags.smin) = ~-1 then flags.smin := !(flags.min);
 if !(flags.minp) && !(flags.minw) then
  failwith "kbo: options -minp and -minw are exclusive";
 let (s,w) = Problem.get_sw p in
 let c = context signature (Trs.funs (Trs.union s w)) in
 Logic.run ~obits:!(flags.ob) (
  Made.run c (encode s w >>= fun phi -> 
  Made.lift (Logic.solve ~solver:c.solver ~goal:None phi) >>= function
   | None -> return None
   | Some ass ->
    decode ass s w >>= fun (s',w') -> 
    decode_af ass s w >>= fun af ->
    decode_intp ass (Trs.union s w) >>= fun intp ->
    decode_prec ass s w >>= fun prec -> 
    decode_ur ass w >>= fun ur ->
    return (Some (make af p (Problem.set_sw s' w' p) prec ur intp))))
;;

(* wrap into state monad *)
let (>>=) = M.(>>=);;
let solve fs p = M.get >>= fun s -> M.return (solve s fs p);;
