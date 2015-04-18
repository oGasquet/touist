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

(*** MODULES (part 1) *********************************************************)
module C = Coefficient;;
module Co = Complexity;;
module Dom = Domain;;
module F = Format;;
module Fun = Function;;
module Number = Logic.Number;;
module NM = Matrix.Make (Number);;
module Intp = Interpretation.Make (NM);;
module Monad = Rewritingx.Monad;;
module NMono = Monomial.Make (NM) (String);;
module NP = Polynomial.Make (NMono);;
module Pos = Position;;
module Sig = Signature;;
module Var = Variable;;
module XO  = XmlOutput;;

module M = struct 
 include Matrix.Make (C);;

 let max = map2 Logic.max;;
 let copy = id;;
 let combine = max;;
 let compare = compare;;
end
module Mono = Monomial.Make (M) (Var);;
module P = Polynomial.Make (Mono);;

(*** TYPES ********************************************************************)
type t = {
 complexity : bool;
 cpx : int option;
 dimension : int; 
 direct : bool; 
 domain : Dom.t;
 monotone : bool;
 temp : int;
 triangle : bool;
 interpretation : Intp.t;
 input : Problem.t;
 output :Problem.t;
 usable_rules : Trs.t option;
 ov : bool;
 poly : bool;
 plstar : bool;
 pleft : bool;
 apc : Logic.Number.t list option;
 dimbnd : bool; (*tmp*)
};;

type inc = A | B | C | E | N;;

type flags = {
 cp : bool ref;
 db : int ref;
 ds2 : bool ref;
 dim : int ref;
 dir : bool ref;
 dp : bool ref;
 help : bool ref;
 inc : inc option ref;
 min : int ref;
 neg : bool ref;
 ob : int ref;
 p : bool ref;
 p2 : bool ref;
 rat : int ref;
 real : bool ref;
 str : bool ref;
 tmp : int ref;
 tri : bool ref;
 ur : bool ref;
 solver : Logic.solver ref;
 (*tmp*)
 overlay : bool ref;
 dimbound: bool ref;
 bound   : int ref;
 explicit : bool ref;
 implicit : bool ref;
 factor : bool ref;
 minpol : bool ref;
 mpd : int ref;
 mul : bool ref;
 diag : bool ref;
 ob2 : int ref;
 sum : int ref;
 nsigma : bool ref;
 jsr : bool ref;
 jsre : bool ref;
 (*confluence*)
 (* ldh : bool ref; *)
 lstar : bool ref;
 left : bool ref;
 strict_empty : bool ref;
};;

type context = {
 arith              : Logic.arith;
 usable             : (Fun.t,Logic.p) Hashtbl.t;
 coefficients       : (Fun.t * int, M.t) Hashtbl.t;
 constants          : (Fun.t,M.t) Hashtbl.t;
 max_matrix         : (M.t * Logic.p) option ref; 
 gt_encodings       : (Rule.t,Logic.p) Hashtbl.t;
 geq_encodings      : (Rule.t,Logic.p) Hashtbl.t;
 state              : Sig.t;
 subterm_encodings  : (Term.t,P.t) Hashtbl.t;
 d_tbl              : (Rule.t * Rule.t * int,M.t) Hashtbl.t; (* distances *)
 graph              : Graph.t;
 constant_encodings : (M.t,M.t) Hashtbl.t; (* experimental *)
 ap                 : Logic.a list ref; (*experimental: coefficients of annihilating polynomial*)
 g3l                : (int*int, Logic.a) Hashtbl.t;
};;

(*** GLOBALS ******************************************************************)
let code = "matrix";;
let name = "Matrix Interpretation Processor";;
let comment = "Applies matrix interpretations."
let keywords = ["matrix interpretation";"linear interpretation";"termination"];;

let flags = {
 cp = ref false;
 db = ref max_int;
 ds2 = ref false;
 dim = ref 1;
 dir = ref false;
 dp = ref false;
 help = ref false;
 inc = ref None;
 min = ref 1;
 neg = ref false;
 ob = ref max_int;
 p  = ref false;
 p2  = ref false;
 rat = ref 1;
 real = ref false;
 tmp = ref 0;
 tri = ref false;
 str = ref false;
 ur = ref false;
 solver = ref Logic.MiniSat;
 (*tmp*)
 overlay = ref false;
 dimbound = ref false;
 bound = ref 0;
 explicit = ref false;
 implicit = ref false;
 factor = ref false;
 minpol = ref false;
 mpd = ref 0;
 mul = ref false;
 diag = ref false;
 ob2   = ref 0;
 sum = ref 0;
 nsigma = ref false;
 jsr = ref false;
 jsre = ref false;
 (*confluence*)
 (* ldh = ref false; *)
 lstar = ref false;
 left = ref false;
 strict_empty = ref false;
};;

let spec =
 let set_inc x _ = flags.inc := Option.some x in
 let spec = [
  ("-cp",Arg.Set flags.cp,"copy oriented rules from strict to weak.");
  ("-db",Arg.Set_int flags.db,"Specifies the bits after the decimal point.");
  ("-d2",Arg.Set flags.ds2,"Add desired2 constraints");
  ("-dim",Arg.Set_int flags.dim,"Specifies the dimension of the matrices.");
  ("-direct",Arg.Set flags.dir,"Tries to finish the termination proof.");
  ("-dp",Arg.Set flags.dp,
   "Allows non-monotone interpretations, i.e., `0' as coefficient.");
  ("--help",Arg.Set flags.help,"Prints information about flags.");
  ("-help",Arg.Set flags.help,"Prints information about flags.");
  ("-h",Arg.Set flags.help,"Prints information about flags.");
  ("-ib",Arg.Int ((:=) flags.min <.> Int.bit_max),
   "Defines the number of bits used to represent matrix entries (same as \
   `-min' but in bits).");
  ("-inca",Arg.Unit (set_inc A),
   "Uses increasing interpretations (minimal cycles).");
  ("-incb",Arg.Unit (set_inc B),
   "Uses increasing interpretations (almost minimal cycles).");
  ("-incc",Arg.Unit (set_inc C),
   "Uses increasing interpretations (compression).");
  ("-ince",Arg.Unit (set_inc E),
   "Uses increasing interpretations (direct, edges).");
  ("-incn",Arg.Unit (set_inc N),
   "Uses increasing interpretations (direct, nodes).");
  ("-max",Arg.Int ((:=) flags.ob <.> Int.bits),
   "Defines the maximum number that can appear as intermediate result.");
  ("-min",Arg.Set_int flags.min,
   "Defines the minimum matrix entry that should be representable.");
  ("-neg",Arg.Set flags.neg,
   "Allow negative numbers (unsound, experimental).");
  ("-ob",Arg.Set_int flags.ob,
   "Defines the number of bits used to represent intermediate results \
    (same as `-max' but in bits)");
  ("-p",Arg.Set flags.p,
   "Print encoding in SMT-LIB format v1.2 and fail");
  ("-p2",Arg.Set flags.p2,
   "Print encoding in SMT-LIB format v2.0 and fail");
  ("-psat",Arg.Unit (Logic.set_print_formula),
   "Print SAT encoding in SMT-LIB format and fail");
  ("-pstat",Arg.Unit (Logic.set_print_stat),
   "Print SAT-solving statistics fail");
  ("-rat",Arg.Set_int flags.rat,"Sets the denumerator.");
  ("-real",Arg.Set flags.real,"Uses reals.");
  ("-strict",Arg.Set flags.str,"Allow constant increase in strict rules.");
  ("-temp",Arg.Set_int flags.tmp,"Experimental.");
  ("-triangle",Arg.Set flags.tri,"Use triangular matrices.");
  ("-ur",Arg.Set flags.ur,"Uses usable rules with respect to interpretation.");
  ("-overlay",Arg.Set flags.overlay,"tmp: overlay matrices for tighter
  complexity bounds (deprecated; has no effect)");
  ("-bound",Arg.Set_int flags.bound,"tmp: bound matrix growth by polynomial of degree [n]");
  ("-explicit",Arg.Set flags.explicit,"tmp: polynomial growth explicit");
  ("-implicit",Arg.Set flags.implicit,"tmp: polynomial growth implicit");
  ("-factor",Arg.Set flags.factor,"tmp: polynomial growth factorization");
  ("-minpol",Arg.Set flags.minpol,"tmp: minimal polynomial");
  ("-mpd",Arg.Set_int flags.mpd,"tmp: degree of minimal polynomial");
  ("-mul",Arg.Set flags.mul,"tmp: polynomial growth reachability");
  ("-diagonal",Arg.Set flags.diag,"tmp: polynomial growth diagonalizable");
  ("-ob2",Arg.Set_int flags.ob2,"tmp: use alternative obits for subformula");
  ("-sum",Arg.Set_int flags.sum,"tmp: limit sum of matrix entries");
  ("-nsigma",Arg.Set flags.nsigma,"tmp: drop closure under substitutions");
  ("-jsr",Arg.Set flags.jsr,"tmp: use joint spectral radius");
  ("-jsre",Arg.Set flags.jsre,"tmp: use together with ``jsr'' (exact bound)");
  ("-minismt",(
   Arg.String (fun mflags -> 
   flags.solver := Logic.MiniSmt (String.split ~d:"_" mflags))
   )
  ,"tmp: use minismt as back-end.");
  (* ("-ldh",Arg.Set flags.ldh,"confluence: label steps with derivation
  height"); *)
  ("-dimbound",Arg.Set flags.dimbound,"tmp: give dimension as complexity
  bound");
  ("-lstar",Arg.Set flags.lstar,"confluence: label steps for star system");
  ("-left",Arg.Set flags.left,"confluence: add label to the left");
  ("-strict_empty",Arg.Set flags.strict_empty ,"confluence: do not fail if strict is empty");
 ] in
 Arg.alignx 80 spec
;;

let help = (comment,keywords,List.map Triple.drop_snd spec);;

(*** MODULES (part 2) *********************************************************)
module Statex = struct type t = context end;;
module Made = Util.Monad.Transformer.State (Statex) (Logic.Monad)
open Made;;

(*** FUNCTIONS ****************************************************************)
let (>>>>=) = Monad.(>>=);;
let (>>>=) = Logic.(>>=);;

let of_int n = Logic.constant (Number.of_int n);;

let init _ =
 flags.cp := false;
 flags.db := max_int;
 flags.ds2 := false;
 flags.dim := 1;
 flags.dir := false;
 flags.dp := false;
 flags.help := false;
 flags.inc := None;
 flags.min := 1;
 flags.neg := false;
 flags.ob := max_int;
 flags.rat := 1;
 flags.real := false;
 flags.str := false;
 flags.tmp := 0;
 flags.tri := false;
 flags.ur := false;
 (*tmp*)
 flags.overlay := false;
 flags.dimbound := false;
 flags.bound := 0;
 flags.explicit := false;
 flags.implicit := false;
 flags.factor := false;
 flags.mul := false;
 flags.diag := false;
 (*confluence*)
 (* flags.ldh := false; *)
 flags.lstar := false;
 flags.left := false;
 flags.strict_empty := false;
;;

(* Constructors and Destructors *)
let make dim dir dom dp cp cpx tmp tri i input output ur o p apc dimbnd = {
 complexity = cp;
 cpx = cpx;
 dimension = dim;
 direct = dir;
 domain = dom;
 monotone = not dp;
 temp = tmp;
 triangle = tri;
 interpretation = i;
 input = input;
 output = output;
 usable_rules = ur;
 ov = o;
 poly = p;
 plstar = !(flags.lstar);
 pleft = !(flags.left);
 apc = apc;
 dimbnd = dimbnd;
};;

let get_ip p = p.input;;
let get_op p = p.output;;

(* Compare Functions *)
let equal p q =
 Problem.equal p.input q.input && Problem.equal p.output q.output
;;

(* Printers *)

let rec eval_const d i = function
 | Term.Var _ -> NP.make [NMono.make (NM.zero d 1) []]
 | Term.Fun (f,ts) ->
  let (cs,c) = 
  (*TODO: this could be exploited to show decreasingness *)
   try Intp.get i f with
    | Failure "missing interpretation" ->
     (List.map (fun _ -> NM.identity d) ts, NM.zero d 1)
  in
  List.foldr2 (fun ci ti -> NP.add (NP.scale ci (eval_const d i ti))) 
   (NP.make [NMono.make c []]) cs ts
;;

let rec interpret_term d i = function
 | Term.Var x ->
  Monad.to_string_var x >>>>= fun x ->
  Monad.return (NP.make [NMono.make (NM.identity d) [x]])
 | Term.Fun (f,ts) ->
  let (cs,c) = Intp.get i f in
  List.foldr2 (fun ci ti ->
   Monad.liftM2 NP.add (Monad.liftM (NP.scale ci) (interpret_term d i ti)))
   (Monad.return (NP.make [NMono.make c []])) cs ts
;;

let interpret_term d i t =
 interpret_term d i t >>>>= fun p ->
 let ms = NP.map (fun m ->
  (NMono.coefficient m,List.join id "*" (NMono.variables m)))
  (NP.non_constant_part p)
 in
 let c =
  try NMono.coefficient (NP.constant_part p)
  with Not_found -> NM.make d 1 Number.zero
 in
 let (cs,xs) = List.split ms in Monad.return (cs,xs,c)
;;

let fprintf_orient d i fmt p =
 let fprintf_rule d i fmt rule =
  interpret_term d i (Rule.lhs rule) >>>>= fun l ->
  interpret_term d i (Rule.rhs rule) >>>>= fun r ->
  Term.to_stringm (Rule.lhs rule) >>>>= fun ls ->
  Term.to_stringm (Rule.rhs rule) >>>>= fun rs ->
  F.fprintf fmt "@[%a@]" NM.fprintf_rule (ls^" = ",l," >= ",r," = "^rs);
  Monad.return ()
 in
 let (s,w) = Problem.get_sw p in
 Monad.fprintf (fprintf_rule d i) "@\n@\n" fmt (Trs.to_list (Trs.union s w))
;;

let fprintf_ur fmt = function
 | None -> Monad.return ()
 | Some trs ->
  F.fprintf fmt "@\n@[<1>usable rules:@\n";
  Trs.fprintfm fmt trs >>>>= fun _ -> Monad.return (F.fprintf fmt "@]")
;;

let max_matrix m0 m1 = NM.map2 Number.max m0 m1;;

let max_i_f _ (coeffs,_) acc = List.foldl max_matrix acc coeffs;;

let max_interpretation d i = Intp.fold max_i_f i (NM.zero d d);;

let fprintf_flags fmt p = 
 F.fprintf fmt "dim=%d" p.dimension;
 if (p.plstar) then 
  Format.fprintf fmt ", lab=%s" (if p.pleft then "left" else "right");
;;

let oi n = Number.of_int n;;
let triple_add (a,b,c) (d,e,f) = (a+d,b+e,c+f);;

(*(-1,1,complex)*)
let rec degree_from_ap = function
 | [] -> (0,0,0)
 | [c;r] -> 
 if Number.is_one c then
  if Number.is_one r then (0,1,0) 
  else if Number.eq r (oi ~-1) then (1,0,0)
  else (0,0,0)
 else (0,0,0)
 | c::p::q::cs ->
  let d = Number.sub (Number.mul p p) (Number.mul (oi 4) q) in
  triple_add (degree_from_ap cs)
  (if Number.eq c Number.one then
   (if Number.eq d Number.zero then
    if Number.eq p (oi 2) then (2,0,0) 
    else if Number.eq p (oi ~-2) then (0,2,0) 
    else (0,0,0)
   else if Number.gt Number.zero d then (0,0,1)
   else (*if Number.gt d Number.zero then*) (1,1,0)
   )
  else (0,0,0)
   )
;;

let degree_from_ap cs = 
 let (a,b,c) = degree_from_ap cs in
 max (max a b) c
;;

let fprintf_ap fmt p =
 match p.apc with 
  | None -> ()
  | Some apc -> 
   let rec fpf fmt = function
    | [] -> ()
    | [c;r] -> if Number.eq c Number.one 
     then F.fprintf fmt "(x - %a)" Logic.Number.fprintf r
     else ()
    | c::p::q::cs -> (if Number.eq c Number.one then
     F.fprintf fmt "(x^2 + %ax + %a)" Logic.Number.fprintf p Logic.Number.fprintf q
     else
     ());
     fpf fmt cs
   in
 F.fprintf fmt "@]@\n@[<1>annihilating monic polynomial:%a@\n" fpf apc;
;;

let fprintf fs fmt p  = 
 F.fprintf fmt "@[<1>%s: %a@\n" name fprintf_flags p;
 fprintf_ur fmt p.usable_rules >>>>= fun _ ->
 if (p.triangle || p.poly) then (
  F.fprintf fmt "@\n@[<1>max_matrix:@\n";
  NM.fprintf fmt (max_interpretation p.dimension p.interpretation);
 );
 fprintf_ap fmt p;
 F.fprintf fmt "@]@\n@[<1>interpretation:@\n";
 Intp.fprintf fmt p.interpretation >>>>= fun _ ->
 F.fprintf fmt "@]@\n@[<1>orientation:@\n";
 fprintf_orient p.dimension p.interpretation fmt p.input >>>>= fun _ ->
 F.fprintf fmt "@]@\n@[<1>problem:@\n";
 Problem.fprintfm fmt p.output >>>>= fun _ ->
 F.fprintf fmt "@]@\n"; List.hd fs fmt >>>>= fun _ ->
 Monad.return (F.fprintf fmt "@]")
;;

let fprintfx_dom p = Dom.fprintfx_domain' (p.domain) (p.dimension);; 

let fprintfx_intp p = XO.node "orderingConstraintProof" [XO.node "redPair" [
  XO.node "interpretation" [
    XO.node "type" [
      XO.node "polynomial" [
        fprintfx_dom p;
        XO.int "degree" 1
      ];
    ];
    (fun fmt -> Intp.fprintfx p.dimension fmt p.interpretation);
  ]]]
;;

let fprintfx_ur = function
  | Some ur -> XO.node "usableRules" [Trs.fprintfx ur]
  | None    -> XO.id
;;

let fprintfx fs p = if Problem.is_dp p.input then (
  let tag = if p.monotone then "monoRedPairProc" else "redPairProc" in
  XO.node tag [
    fprintfx_intp p;
    Problem.fprintfx p.output;
    fprintfx_ur p.usable_rules;
    List.hd fs]
) else if Problem.is_sp p.input || Problem.is_rp p.input then (
  XO.node "ruleRemoval" [
    fprintfx_intp p;
    Problem.fprintfx p.output;
    List.hd fs]
) else if Problem.is_cp p.input then (
  XO.node "ruleShifting" [
    fprintfx_intp p;
    (* compute the removed rules *)
    ( let is,iw = Problem.get_sw p.input in
      let os,ow = Problem.get_sw p.output in
      let diff = Trs.diff is os in
      XO.node "trs" [Trs.fprintfx diff]);
    List.hd fs]
) else (
  failwith "MatrixInterpretation.fprintfx: XML output not supported"
)
;;


(* Processor *)
(* administrative functions *)
let (>>=) = Made.(>>=);;

let context state problem =
 let (s,_) = Pair.map Trs.to_list (Problem.get_sw problem) in
 let g =
  try match Problem.get_dg problem with 
   | Problem.Complete -> Graph.generate (fun n m -> [(n,m)]) s 
   | Problem.Partial x -> x
  with Failure _ -> Graph.generate (fun _ _ -> []) []
 in
 let g = Graph.restrict s g in
 let arith = {
  Logic.min = Int64.of_int !(flags.min);
  neg       = !(flags.neg);
  rat       = !(flags.rat);
  real      = !(flags.real);
  minf      = false}
 in
 {arith              = arith;
  usable             = Hashtbl.create 512;
  coefficients       = Hashtbl.create 512;
  constants          = Hashtbl.create 512;
  max_matrix         = ref None;
  gt_encodings       = Hashtbl.create 512;
  geq_encodings      = Hashtbl.create 512;
  state              = state;
  subterm_encodings  = Hashtbl.create 512;
  d_tbl              = Hashtbl.create 512;
  graph              = g;
  constant_encodings = Hashtbl.create 512;
  ap                 = ref [];
  g3l                = Hashtbl.create 512;
 };;

let cache_m tbl f k = 
 if Hashtbl.mem tbl k then return (Hashtbl.find tbl k)
 else (f k >>= fun v -> (Hashtbl.add tbl k v; return v))
;;

let big_add xs = List.foldl (<+>) Logic.zero xs;;
(* functions lifted from Logic into Made *)
let fresh_arith = get >>= fun s -> lift (Logic.fresh_arith s.arith);;
let fresh_arith_spec arith = lift (Logic.fresh_arith arith);;
let fresh_bool = get >>= fun s -> lift Logic.fresh_bool;;
let ($&$) = liftM2 (<&>);;
let ($|$) = liftM2 (<|>);;
let ($->$) = liftM2 (<->>);;
let ($<$) = liftM2 (<<>);;
let ($>$) = liftM2 (<>>);;
let ($>=$) = liftM2 (<>=>);;
let ($<=$) = liftM2 (<<=>);;
let ($=$) = liftM2 (<=>);;
let ($+$) = liftM2 (<<>);;
let eval_a a ass = a >>= fun a -> lift (Logic.eval_a a ass);;
let eval_p p ass = p >>= fun p -> lift (Logic.eval_p p ass);;
let map_op op f ls = sequence (List.map f ls) >>= (return <.> op);;
let mapi_op op f ls = sequence (List.mapi f ls) >>= (return <.> op);;
let gen_op op f n = sequence (List.gen f n) >>= (return <.> op);;
let map_and f = map_op Logic.big_and f;;
let map_add f = map_op big_add f;;
let mapi_and f = mapi_op Logic.big_and f;;
let gen_and f = gen_op Logic.big_and f;;
let gen_add f = gen_op big_add f;;
let map_or f = map_op Logic.big_or f;;
let mapi_or f = mapi_op Logic.big_or f;;
let gen_or f = gen_op Logic.big_or f;;

(* state monad interaction *)
let is_dp f = get >>= fun c -> return (Sig.is_dp f c.state);;
let name f = get >>= fun c -> return (Sig.find_fun_name f c.state);;
let arity f = 
 (* name f >>= fun n -> Format.printf "f = %s@\n%!" n; *)
 get >>= fun c -> return (Sig.find_ari f c.state);;

let get_state c = c.state;;
let set_state s c = 
 {c with state = s}
;;

(* interaction with signature *)
let rec get_vars n = 
 if n = 0 then return []
 else
  get >>= fun c -> let x,s = Sig.fresh_var (get_state c) in
  let (_,s) = Sig.create_var_name x s in
  set (set_state s c) >>
  get_vars (n-1) >>= fun xs ->
  return (x::xs)
;;

let get_fun n =
 get >>= fun c -> let f,s = Sig.fresh_fun (get_state c) in
 let s = Sig.add_ari f n s in
 let _,s = Sig.create_fun_name f s in
 set (set_state s c) >>
 return f
;;

(* lift function from Rewriting Monad into Made *)
let lift_monad f = get >>= fun c ->
 let Right (v,state) = Monad.eval (get_state c) f in
 ignore (set_state state c);
 return v;
;;

(* matrix encoding starts here *)
let gen fresh triangle poly tmp m n k = get >>= fun c ->
 let i,j = k / m, k mod n in
 if triangle && i > j then return Logic.zero
 else if tmp = 3 && i > j then return Logic.zero
 else if tmp = 4 && i > j+1 then return Logic.zero
 else if (triangle || poly) && i = j then
  (*restrict to 1*)
  fresh_arith_spec {c.arith with Logic.min = Int64.of_int c.arith.Logic.rat}
 else if tmp <> 0 && i = 0 && j = 0 then
  return Logic.one
 else if tmp = 1 && i = 0 then 
  return Logic.zero
 else if tmp = 2 && j = 0 then 
  return Logic.zero
 else fresh
;;

let make_matrix ?(fresh=fresh_arith) triangle poly tmp m n = 
 Made.sequence (List.gen (gen fresh triangle poly tmp m n) (m*n)) >>=
 (return <.> M.of_list m n)
;;

let poly_complexity flags = 
 !(flags.tri) || !(flags.explicit) || !(flags.implicit) ||
 !(flags.factor) || !(flags.mul) || !(flags.diag) ||
 !(flags.minpol) || !(flags.jsr)
;;

let make_coefficient f i = get >>= fun c ->
 is_dp f >>= fun b -> 
 let d = if b then 1 else !(flags.dim) in
 make_matrix !(flags.tri) (poly_complexity flags) !(flags.tmp) d !(flags.dim)
;;

let make_constant f = get >>= fun c ->
 is_dp f >>= fun b -> 
 let d = if b then 1 else !(flags.dim) in
 make_matrix false false 0 d 1
;;

let coefficient f i = get >>= fun c ->
 cache_m c.coefficients (uncurry make_coefficient) (f, i)
;;

let coefficients f = arity f >>= fun a ->
 Made.sequence (List.gen (coefficient f) a)
;;

let matrices fs = Made.flat_map coefficients fs;;

let constant f = get >>= fun c -> cache_m c.constants make_constant f;;

let u t = get >>= fun c ->
          cache_m c.usable (const fresh_bool) (Option.the(Term.root t));;

let rec encode_term t = get >>= fun c ->
 cache_m c.subterm_encodings (etc c) t
and etc c = function
 | Term.Var x -> return (P.make [
  Mono.make (M.identity !(flags.dim)) [x];
  Mono.make (M.make !(flags.dim) 1 Logic.zero) []])
 | Term.Fun (f, ts) ->
  (List.fold_lefti (fun i p t -> 
   liftM2 P.add p (liftM2 P.scale (coefficient f i) (encode_term t)))
  (liftM P.make (sequence [liftM2 Mono.make (constant f) (return [])]))
  ts)
;;

let equal_matrix m0 m1 = Logic.big_and (M.map2list C.eq m0 m1);;
let greater_equal_matrix m0 m1 = Logic.big_and (M.map2list C.geq m0 m1);;

let greater_matrix m0 m1 = 
 (C.gt (M.get 0 0 m0) (M.get 0 0 m1)) <&> (greater_equal_matrix m0 m1)
;;

let greater_equal_mono m0 m1 =
 greater_equal_matrix (Mono.coefficient m0) (Mono.coefficient m1)
;;

let greater_mono m0 m1 =
 greater_matrix (Mono.coefficient m0) (Mono.coefficient m1)
;;

let extend_vars r c p xs = 
 let z = M.zero r c in
 List.foldr (fun x -> P.add (P.make [Mono.make z x])) p xs
;;

let dim p0 p1 = 
 (*List.hd throws exception if lhs and rhs do not have constants;
   but then we do not extend any pi *)
 try 
  let (p0,p1) = Pair.map P.non_constant_part (p0,p1) in
  let c = List.hd (P.coefficients p0 @ P.coefficients p1) in
  (M.rows c, M.columns c)
 with Failure "hd" -> (0,0);  
;;

let same_variables p0 p1 =
 let (r,c) = dim p0 p1 in
 let v0,v1 = Pair.map P.variables (p0,p1) in
 let x0,x1 = List.diff v1 v0, List.diff v0 v1 in
 (extend_vars r c p0 x0, extend_vars r c p1 x1)
;;

let greater_poly p0 p1 = 
 let c0 = P.constant_part p0 in
 let c1 = try P.constant_part p1 with Not_found -> 
  let m = Mono.coefficient c0 in
  Mono.make (M.zero (M.rows m) (M.columns m)) []
 in
 let (nc0,nc1) = Pair.map P.non_constant_part (p0,p1) in
 let (nc0,nc1) = same_variables nc0 nc1 in
 let cs = 
  if !(flags.nsigma) then [Logic.top] else P.map2 greater_equal_mono nc0 nc1
 in
 let cs' = greater_mono c0 c1 in
 Logic.big_and (cs'::cs)
;;

let greater_equal_poly ?(inc=None) p0 p1 =
 let (p0,p1) = same_variables p0 p1 in
 let (p0,p1) =
  if inc = None then (p0,p1) else Pair.map P.non_constant_part (p0,p1)
 in
 if !(flags.nsigma) then 
  let (c0,c1) = Pair.map P.constant_part (p0,p1) in
  greater_equal_mono c0 c1
 else
  Logic.big_and (P.map2 greater_equal_mono p0 p1)
;; 

let greater_equal_rule ?(inc=None) rule = 
 liftM2 (greater_equal_poly ~inc:inc) (encode_term (Rule.lhs rule))
  (encode_term (Rule.rhs rule))
;;

let greater_equal_rule_s ?(inc=None) rule = 
 let ncp = P.non_constant_part in
 encode_term (Rule.lhs rule) >>= fun l ->
 encode_term (Rule.rhs rule) >>= fun r ->
 return (greater_equal_poly ~inc:inc (ncp l) (ncp r)) 
;;

let greater_equal_rule ?(inc=None) rule = get >>= fun c ->
 cache_m c.geq_encodings (greater_equal_rule ~inc:inc) rule
;;

let greater_rule rule =
 liftM2 greater_poly (encode_term (Rule.lhs rule))
  (encode_term (Rule.rhs rule))
;;

let greater_rule ?(inc=None) rule = get >>= fun c ->
 cache_m c.gt_encodings greater_rule rule
;;

let mon_m m = return (C.geq (M.get 0 0 m) C.one);;

let mon fs = matrices fs >>= fun ms -> map_and mon_m ms;;

let triangle_m m = get >>= fun s ->
 return (Logic.big_and (List.gen (fun i -> C.geq C.one (M.get i i m)) !(flags.dim)))
;;

let triangle fs = matrices fs >>= fun ms -> map_and triangle_m ms;;

(* not zero matrix *)
let nzm f i =
 coefficient f i >>= fun c ->
 let zm = M.fold (fun elt -> (<&>) (C.eq elt C.zero)) c Logic.top in
 return (Logic.neg zm)
;;

(* stuff for usable rules w.r.t. interpretation similar to GI03_01 *)
let rec process_rule df rule =
 let (l,r)  = Rule.to_terms rule in
 let dp = List.flat_map (flip Term.fun_pos r) df in
 let rec conj_of_smaller_pos p r =
 if p = Pos.root then return Logic.top else
  let q, i = Pos.split_last p in
  ((nzm (Option.the(Term.root (Term.subterm q r))) i)
    $&$ (conj_of_smaller_pos q r))
 in
 (u l) $->$ 
  map_and (fun p -> (conj_of_smaller_pos p r) $->$ (u (Term.subterm p r))) dp
;;

let geq_ur op geq rule = liftM2 op (u(Rule.lhs rule)) (geq rule);;

let encode_geq s w = get >>= fun c ->
 (* old let s = if !(flags.str) then [] else s in *)
 (*HZ: do not orient weak rules strict*)
 (* let geq = if !(flags.dir) then greater_rule else greater_equal_rule in *)
 let geq = greater_equal_rule in
 let geqs = if !(flags.str) then greater_equal_rule_s else geq in
 if !(flags.ur) then (
  let ds = Trs.def_symbols (Trs.of_list (s@w)) in
  map_and (geq_ur (<&>) (geq ~inc:!(flags.inc))) s $&$
  map_and (geq_ur (<->>) geq) w $&$
  map_and (process_rule ds) (s@w) 
 ) else 
  map_and geqs s $&$ map_and geq w
;;

(* increasing interpretations begin *)
module Lgraph = Util.Graph.Labeled (M) (Rule);;

module N = struct
 include Number;;
 let copy = id;;
 let compare a b = if a < b then ~-1 else if a > b then 1 else 0;;
 let combine = Number.max;;
end

module Ngraph = Util.Graph.Labeled (N) (Rule);;

let m110 = M.make 1 1 Logic.zero;;
let m111 = M.make 1 1 Logic.one;;
let m11m = M.make 1 1 Logic.minf;;
let encode_cp t = liftM Mono.coefficient (liftM P.constant_part (encode_term t));;

(*compare to non-caching *)
let cc x = get >>= fun c ->
 let a = {c.arith with Logic.neg=true} in
 let a = {a with Logic.min= Int64.succ a.Logic.min} in
 cache_m c.constant_encodings (fun _ ->
  (make_matrix false false 0 ~fresh:(fresh_arith_spec a) 1 1)) x
;;

let cc x = return x;;
 
let get_cc () = get >>= fun c -> return 
 (Hashtbl.fold (fun k v acc -> (equal_matrix k v) <&> acc)
  c.constant_encodings Logic.top)
;;

let sub a b = M.add a (M.scale Logic.minus_one b);;

let delta r = 
 encode_cp (Rule.lhs r) >>= fun a -> 
 encode_cp (Rule.rhs r) >>= fun b ->
 return (sub b a);;

let delta_inv r = 
 encode_cp (Rule.lhs r) >>= fun a -> 
 encode_cp (Rule.rhs r) >>= fun b ->
 return (sub a b);;

let label_edge (a,b) = 
 delta a >>= fun d ->
 return (a,Some d,b)
;;

let label_graph g = 
 sequence (List.map label_edge (Graph.to_list g)) >>=
 (return <.> Lgraph.of_list)
;;

let big_sum1 xs = List.foldr (M.add) m110 xs;;
let neg_filter f = List.filter (fun x -> not (f x));; 

(*r_abi variables*)
let set_d a b i r = get >>= fun c ->
 if (Hashtbl.mem c.d_tbl (a,b,i)) then failwith "set_d";
 Hashtbl.add c.d_tbl (a,b,i) r;
 return ()
;;

let get_d a b i = get >>= fun c ->
 if not (Hashtbl.mem c.d_tbl (a,b,i)) then failwith "get_d";
 return (Hashtbl.find c.d_tbl (a,b,i))
;;

(** [enk g] returns [k] indicating number of transitivity updates
necessary for transitivity closure *)
let enk g = Int.bits (Lgraph.size_nodes g) - 1;;

(* returns formula that expresses that [b] is reachable from 
[a] in at most [2^i] steps (implicitly computes maximal distance
between [a] and [b] *)
let reachable i ns (a,b) = 
 List.fold_right
  (fun n -> liftM2 M.max (liftM2 M.add (get_d a n (i-1)) (get_d n b (i-1))))
  ns
  (get_d a b (i-1)) >>= fun di ->
  (* abbreviate every fourth variable *)
 (if i mod 4 = 1 then cc di else return di) >>= fun di ->
 set_d a b i di
;;

let rec tc i k ns = 
 if i > k then return () else
  let nss = List.square ns in
  sequence (List.map (reachable i ns) nss) >> tc (i+1) k ns
;;

let transitive_closure k ldg = 
  let ns, es = Lgraph.nodes ldg, Lgraph.edges ldg in
  let nes = List.diff (List.square ns) (List.map (fun (a,_,b) -> (a,b)) es) in
  (* edges that do exist have distance [r] *)
  sequence (List.map (fun (a,r,b) -> (set_d a b 0 (Option.the r))) es) >>
  (* edges that do not exist have distance -infinity *)
  sequence (List.map (fun (a,b) -> (set_d a b 0 m11m)) nes) >>
  tc 1 (enk ldg) (Lgraph.nodes ldg)
;;

let label_graph dg = 
 sequence (List.map (fun (a,b) -> delta a >>= fun x -> return (a,Some x,b))
 (Graph.edges dg)) >>= fun ws -> return (Lgraph.of_list ws)
;;

(* construct unlabeled graph *)
let unlabel_graph g =
 Graph.of_list (List.map (fun (a,_,b) -> (a,b)) (Lgraph.edges g))
;;

let encode_direct_node ldg = ldg >>= fun ldg ->
 let k = enk ldg in 
 let ns = Lgraph.nodes ldg in
 transitive_closure k ldg >>
 map_and (fun n -> liftM2 greater_equal_matrix (return m110) (get_d n n k)) ns
 $&$ map_or (fun n -> liftM2 greater_matrix (return m110) (get_d n n k)) ns
 $&$ (get_cc ())
;;

let decode_direct_node ass p = get >>= fun c -> 
 label_graph c.graph >>= fun ldg ->
 let (s,_) = Problem.get_sw p in
 let k = enk ldg in
 Made.filter 
  (fun r -> eval_p (liftM2 greater_equal_matrix (get_d r r k) (return m110)) ass)
  (Trs.to_list s) >>= fun rules ->
 return (Problem.set_dps (Trs.of_list rules) p)
;;

let encode_direct_edge ldg = ldg >>= fun ldg ->
 let k = enk ldg in 
 let ns, es = Lgraph.nodes ldg, Lgraph.edges ldg in
 transitive_closure k ldg >>
 map_and (fun n -> liftM2 greater_equal_matrix (return m110) (get_d n n k)) ns
 $&$ map_or (fun (a,l,b) -> liftM2 greater_matrix (return m110) 
  (liftM2 M.add (return (Option.the l)) (get_d b a k))) es
 $&$ (get_cc ())
;;

let decode_direct_edge ass p = get >>= fun c ->
 decode_direct_node ass p >>= fun p' ->
 (*if Problem.equal p p' then ( (* remove edges only if no node
 removed *) *)
  label_graph c.graph >>= fun ldg ->
  let k = enk ldg in
  Made.filter (fun (a,l,b) ->
   liftM2 Number.gt (return Number.zero) (eval_a (liftM (M.get 0 0) (liftM2
   M.add (return (Option.the l)) (get_d b a k))) ass))
   (Lgraph.edges ldg) >>= fun es ->
  let dg' =
   List.fold_right (fun (a,_,b) -> (Graph.remove_edge (a,b))) es c.graph
  in
  return (Problem.update_dg (Problem.Partial dg') p')
 (* ) else *)
  (*return p' *)
;;

(*minimal cycles*)
let is_minimal_cycle g = 
 List.length (Graph.sccs ~trivial:false g) = 1 &&
 List.length (Graph.edges g) = List.length (Graph.nodes g)
;;

let minimal_cycle s = get >>= fun c -> let g = c.graph in
 if is_minimal_cycle g then 
  liftM2 greater_matrix  
   (map_op big_sum1 encode_cp (List.map Rule.lhs s)) 
    (map_op big_sum1 encode_cp (List.map Rule.rhs s))
 else
  return Logic.bot
;;

(*almost minimal cycles*)
let almost_minimal_cycle g s r = 
 let es = List.map (fun rule -> (r,rule)) s in
 let g' = List.foldl (flip Graph.remove_edge) g es in
 Graph.sccs ~trivial:false g' = []
;;

let ito ma = ma >>= fun a -> 
 return (Logic.ite (greater_matrix a m110) Logic.one Logic.zero)
;;

let almost_minimal_cycle s = get >>= fun c -> let g = c.graph in
 let (selected,rest) = List.partition (almost_minimal_cycle g s) s in
 map_op big_sum1 delta_inv selected >>= fun left ->
 map_op big_sum1 (fun r -> liftM2 M.scale (ito (delta r)) (delta r)) rest >>=
  fun right -> return (greater_matrix left right)
;;

(*compression algorithm*)
let deg_sort (_,d0) (_,d1) = compare d0 d1;;

let degree_ii p n g =
 List.length (List.filter (fun e -> p e = n) (Lgraph.edges g))
;;

let choose_node g =
 let ns = Lgraph.nodes g in
 let d n = degree_ii Triple.fst n g * degree_ii Triple.thd n g in
 match List.sort deg_sort (List.map (fun n -> (n, d n)) ns) with
  | [] -> failwith "choose_node"
  | (n,_) :: ns -> n
;;

let alg g = 
 let rec alg acc g = acc >>= fun acc ->
  if Lgraph.is_empty g then
   return acc
  else
   let id, g' = Lgraph.partition (fun (n,_,m) -> n = m) g in
   let acc = List.map (Option.the <.> Triple.snd) (Lgraph.edges id) @ acc in
   let n = choose_node g' in
   let g = Lgraph.combine_edges (Lgraph.bypass n g') in
   let wes = Lgraph.edges g in
   sequence (List.map (fun ((a,l,b) as e) -> 
   (*abbreviate variable *)
   (if Lgraph.mem_edge e g then return (Option.the l)
   else cc (Option.the l)) >>= fun l -> 
   return (a,Some l,b)) wes) >>= fun wes -> 
   let g = Lgraph.of_list wes in
   alg (return acc) g
 in
 alg (return []) g
;;

let encode_compress ldg = ldg >>= fun ldg ->
 alg ldg >>= fun cs ->
 get >>= fun c ->
 let cs = List.map return cs in
 (map_or (liftM2 greater_matrix (return m110)) cs) 
  $&$ (map_and (liftM2 greater_equal_matrix (return m110)) cs)
  $&$ get_cc ()
;;

let eval_graph ldg ass =
 let ws = Lgraph.edges ldg in
 sequence (List.map
  (fun (a,l,b) -> 
   eval_a (return (M.get 0 0 (Option.the l))) ass >>= fun l ->
   return (a,Some l,b)) ws) >>= fun wes ->
 return (Ngraph.of_list wes)
;;

let decode_compress_node ass p = get >>= fun c ->
 label_graph c.graph >>= flip eval_graph ass >>= fun g ->
 let n = Int.bits (Ngraph.size_nodes g) - 1 in
 let g = Ngraph.transitive_closure ~n:n g in
 let rules = List.filter
  ((fun (a,l,b) -> a = b && N.eq N.zero (Option.the l)))
  (Ngraph.edges g)
 in
 return (Problem.set_dps (Trs.of_list (List.map Triple.fst rules)) p)
;;

let find_label (a,b) g = 
 Option.the (Triple.snd (List.find (fun (x,_,y) -> a=x && b=y)
  (Ngraph.edges g)))
;;

(* find lonely edges *)
let rec cost p g = match p with
 | [] -> failwith "cost: empty path"
 | [a] -> N.zero
 | a :: b :: ps -> N.add (find_label (a,b) g) (cost (b::ps) g)
;;

let maximal_path a b g = 
 let pss = Ngraph.paths a b g in
 let ps = List.hd pss in
 List.fold_left
  (fun acc p -> 
   let c = cost p g in
   if N.gt (snd acc) c then acc else (p, c)
  )
  (ps, cost ps g)
  (List.tl pss)
;;

let is_lonely_edge (a,l,b) g =
 if a = b then N.gt N.zero (Option.the l) else
 let lm =
  Triple.snd (List.find (fun (x,_,y) -> (x,y)=(b,a)) (Ngraph.edges g))
 in
 N.gt N.zero (N.add (Option.the l) (Option.the lm))
;;

let decode_compress_edge ass p = get >>= fun c ->
 decode_compress_node ass p >>= fun p' -> 
 if Problem.equal p p' then
  label_graph c.graph >>= flip eval_graph ass >>= fun vdg ->
  let n = Int.bits (Ngraph.size_nodes vdg) - 1 in
  let tdg = Ngraph.transitive_closure ~n:n vdg in
  let es = List.filter (flip is_lonely_edge tdg) (Ngraph.edges vdg) in
  let g' =
   List.fold_right Graph.remove_edge (List.map Triple.drop_snd es) c.graph
  in
  return (Problem.update_dg (Problem.Partial g') p')
 else return p'
;;

(* increasing interpretations end *)

(* complexity encodings begin *)
(*
 (* horribly large encoding *)
let max_matrix m0 m1 = M.max m0 m1;;

let max_matrix fs = get >>= fun c -> 
 Made.sequence (List.map coefficients fs) >>= fun ms ->
 Made.return (List.foldl max_matrix (M.zero !(flags.dim) !(flags.dim)) (List.concat ms))
;;
*)

let max_matrix fs = get >>= fun c ->
 match !(c.max_matrix) with
  | None -> let p = poly_complexity flags in
   make_matrix !(flags.tri) p !(flags.tmp) !(flags.dim) !(flags.dim) >>= fun m ->
   matrices fs >>= fun ms ->
   let cs = Logic.big_and (List.map (greater_equal_matrix m) ms) in
   c.max_matrix := Some (m, cs);
   Made.return m
  | Some (m,_) -> Made.return m

(* demand non-one in diagonal *)
let ito x = Logic.ite x Logic.one Logic.zero;;

let count_diagonal_ones m = 
 gen_add (fun i -> return (ito (M.get i i m <=> Logic.one))) !(flags.dim);;

let diagonal_ok m = gen_and (fun i -> return (M.get i i m <<=> Logic.one)) !(flags.dim);;

let count_ones n fs = max_matrix fs >>= fun m ->
 (return (Logic.constant (Number.of_int n)) $>=$ count_diagonal_ones m)
;;

(*explicit approach*)
let explicit_1 m = 
 let a = M.get 0 0 m in
 Made.return (a <<=> Logic.one)
;;

let explicit_2 m = 
 let a = M.get 0 0 m and b = M.get 0 1 m 
 and c = M.get 1 0 m and d = M.get 1 1 m in
 Made.return (
  ((a <+> d) <<=> of_int 2) <&>
  ((a <+> d <+> (b<*>c)) <<=> ((a<*>d) <+> Logic.one))
 )
;;

(*
(* real eigenvalues only *)
let explicit_3 m = 
 let a = M.get 0 0 m and b = M.get 0 1 m and c = M.get 0 2 m in
 let d = M.get 1 0 m and e = M.get 1 1 m and f = M.get 1 2 m in
 let g = M.get 2 0 m and h = M.get 2 1 m and i = M.get 2 2 m in
 fresh_arith >>= fun l1 -> fresh_arith >>= fun l2 -> fresh_arith >>= fun l3 -> 
 Made.return (
  (Logic.zero <<=> l1) <&> (l1 <<=> Logic.one) <&>
  (Logic.zero <<=> l2) <&> (l2 <<=> Logic.one) <&>
  (Logic.zero <<=> l3) <&> (l3 <<=> Logic.one) <&>
  ((l1 <+> l2 <+> l3) <=> (a <+> e <+> i)) <&>
  (((l1<*>l2) <+> (l1<*>l3) <+> (l2<*>l3) <+> (f<*>h) <+> (c<*>g) <+> (b<*>d)) <=>
   ((e<*>i) <+> (a<*>i) <+> (a<*>e))) <&>
  (((l1<*>l2<*>l3) <+> (c<*>e<*>g) <+> (b<*>d<*>i) <+> (a<*>f<*>h)) <=>
   ((a<*>e<*>i) <+> (b<*>f<*>g) <+> (c<*>d<*>h)))
 )
;;
*)


(* complex eigenvalues (no system applies) *)
(*
let explicit_3 m = 
 let a = M.get 0 0 m and b = M.get 0 1 m and c = M.get 0 2 m in
 let d = M.get 1 0 m and e = M.get 1 1 m and f = M.get 1 2 m in
 let g = M.get 2 0 m and h = M.get 2 1 m and i = M.get 2 2 m in
 fresh_arith_spec (Logic.nat 1) >>= fun l1 -> 
 fresh_arith_spec (Logic.int 2) >>= fun p -> 
 fresh_arith_spec (Logic.int 3) >>= fun q -> 
 Made.return (
  (Logic.one <<=> l1) <&> (l1 <<=> Logic.one) <&>
  (l1 <=> (a <+> e <+> i <+> p)) <&>
  ((q <+> (f<*>h) <+> (c<*>g) <+> (b<*>d)) <=>
   ((p<*>l1) <+> (e<*>i) <+> (a<*>i) <+> (a<*>e))) <&>
  (((l1<*>q) <+> (c<*>e<*>g) <+> (b<*>d<*>i) <+> (a<*>f<*>h)) <=>
   ((a<*>e<*>i) <+> (b<*>f<*>g) <+> (c<*>d<*>h))) <&>
   (p<*>p <<> ((of_int 4)<*>q)) <&>
  ((of_int ~-2) <<=> p) <&> (p <<=> (of_int 2)) <&>
  (((p<*>p) <+> (of_int 2 <*> q)) <<=> of_int 2) <&>
  (of_int 0 <<=> ((p<*>p) <+> (of_int 2 <*> q) <+> of_int 2))
 )
;;
*)

let explicit fs = max_matrix fs >>= fun m -> match !(flags.dim) with
 | 1 -> explicit_1 m
 | 2 -> explicit_2 m
 | _ -> failwith "matrix -explicit: too large dimension"
;;

(* implicit approach *)
let implicit_1 m =
 let a = M.get 0 0 m in
 Made.return ((a <<=> Logic.one))
;;

let implicit_2 m =
 let a = M.get 0 0 m and b = M.get 0 1 m in
 let c = M.get 1 0 m and d = M.get 1 1 m in
 Made.return (
  ((Logic.one <+> (a<*>d))  <>=> ((b<*>c)<+>a<+>d)) <&>
  ((Logic.one <+> (a<*>d) <+> a <+> d)  <>=> (b<*>c))
 )
;;

let implicit_3 m =
 let a = M.get 0 0 m and b = M.get 0 1 m and c = M.get 0 2 m in
 let d = M.get 1 0 m and e = M.get 1 1 m and f = M.get 1 2 m in
 let g = M.get 2 0 m and h = M.get 2 1 m and i = M.get 2 2 m in
 let p = Logic.zero <-> (a <+> e <+> i) in
 let q = ((e<*>i)<+>(a<*>i)<+>(a<*>e)) <-> ((f<*>h)<+>(c<*>g)<+>(b<*>d)) in
 let r = ((c<*>e<*>g)<+>(b<*>d<*>i)<+>(a<*>f<*>h)) <-> 
         ((a<*>e<*>i)<+>(b<*>f<*>g)<+>(c<*>d<*>h)) in
 let chia_m1 = (of_int ~-1 <+> p <+> r) <-> q in
 let chia_p1 = of_int 1 <+> p <+> q <+> r in
 let chia_prime = 
  ((p<*>p) <<> (of_int 3 <*> q)) <|> (
   (of_int ~-3 <<=> p) <&> (p <<=> of_int 3) <&>
   ((Logic.zero <<=> ((of_int 2<*>p) <+> (q <+> of_int 3)))) <&>
   ((of_int 2<*> p) <<=> (q <+> of_int 3))
  ) in
 Made.return (
  (chia_m1 <<=> Logic.zero) <&>
  (chia_p1 <>=> Logic.zero) <&>
  (
  (* complex eigenvalues (do they occur?)*)
    (* (disc <<> Logic.zero) <|>  *)
  Logic.bot <|>
  chia_prime 
  ))
;;

let implicit fs = max_matrix fs >>= fun m -> match !(flags.dim) with
 | 1 -> implicit_1 m
 | 2 -> implicit_2 m
 | 3 -> implicit_3 m
 | _ -> failwith "matrix -implicit: wrong dimension"
;;

(* approach by factorization *)
let factor_lin r = (of_int ~-1 <<=> r) <&> (r <<=> of_int 1);;

let factor_quad p q = 
 let aux1 = 
  ((p<*>p) <>=> (of_int 4 <*> q))
  <->> (
  (Logic.zero <<=> (p <+> of_int 2)) <&>
  (p <<=> of_int 2) <&>
  (Logic.zero <<=> (p<+>q<+>Logic.one)) <&>
  (p <<=> (q<+>Logic.one))
  ) in
 let aux2 = 
  ((p<*>p) <<> (of_int 4 <*> q))
  <->> (
  (q <<=> Logic.one)
  ) in
aux1 <&> aux2
;;

let factor_1 p m = 
 let a = M.get 0 0 m in
 let zero = (p <=> a) in
 factor_lin p <&> zero;;

let factor_2 p q m = 
 let a = M.get 0 0 m and b = M.get 0 1 m in
 let c = M.get 1 0 m and d = M.get 1 1 m in
 let one = (p <+> a <+> d) <=> Logic.zero in
 let zero = (q <+> (b<*>c)) <=> (a<*>d) in
 factor_quad p q <&> zero <&> one
;;

let factor_3 p q r m = 
 let a = M.get 0 0 m and b = M.get 0 1 m and c = M.get 0 2 m in
 let d = M.get 1 0 m and e = M.get 1 1 m and f = M.get 1 2 m in
 let g = M.get 2 0 m and h = M.get 2 1 m and i = M.get 2 2 m in
 let two = r <=> (a <+> e <+> i <+> p) in
 let one = (q <+> (f<*>h) <+> (c<*>g) <+> (b<*>d)) <=> 
           ((p<*>r) <+> (e<*>i) <+> (a<*>i) <+> (a<*>e)) in
 let zero= ((r<*>q) <+> (c<*>e<*>g) <+> (b<*>d<*>i) <+> (a<*>f<*>h)) <=>
           ((a<*>e<*>i) <+> (b<*>f<*>g) <+> (c<*>d<*>h)) in
 factor_quad p q <&> factor_lin r <&> zero <&> one <&> two
;;

let factor_4 p q r s m = 
 let a = M.get 0 0 m and b = M.get 0 1 m and c = M.get 0 2 m  and d = M.get 0 3 m in
 let e = M.get 1 0 m and f = M.get 1 1 m and g = M.get 1 2 m  and h = M.get 1 3 m in
 let i = M.get 2 0 m and j = M.get 2 1 m and k = M.get 2 2 m  and l = M.get 2 3 m in
 let m = M.get 3 0 m and n = M.get 3 1 m and o = M.get 3 2 m  and u = M.get 3 3 m in
 let three = 
  (u <+> k <+> f <+> a <+> 
  r <+> p)
  <=> 
  Logic.zero
 in
 let two = 
  ((m<*>d) <+> (n<*>h) <+> (o<*>l) <+> (i<*>c) <+> (j<*>g) <+> (e<*>b) <+>
  s <+> q <+> (p<*>r))
  <=>
  ((u<*>k) <+> (u<*>f) <+> (u<*>a) <+> (k<*>f) <+> (k<*>a) <+> (f<*>a))
 in
 let one =
  ((i<*>b<*>g) <+> (j<*>e<*>c) <+> (k<*>f<*>a) <+> (m<*>b<*>h) <+>
  (m<*>c<*>l) <+> (n<*>e<*>d) <+> (n<*>g<*>l) <+> (o<*>i<*>d) <+>
  (o<*>j<*>h) <+> (u<*>k<*>f) <+> (u<*>k<*>a) <+> (u<*>f<*>a) <+>
  (r<*>q) <+> (p<*>s))
  <=> 
  ((i<*>c<*>f) <+> (j<*>g<*>a) <+> (k<*>e<*>b) <+> (m<*>d<*>k) <+>
  (m<*>d<*>f) <+> (n<*>h<*>k) <+> (n<*>h<*>a) <+> (o<*>l<*>f) <+>
  (o<*>l<*>a) <+> (u<*>i<*>c) <+> (u<*>j<*>g) <+> (u<*>e<*>b))
 in
 let zero =
  ((m<*>b<*>g<*>l) <+> (m<*>c<*>j<*>h) <+> (n<*>e<*>c<*>l) <+>
  (n<*>g<*>i<*>d) <+> (o<*>i<*>b<*>h) <+> (o<*>j<*>e<*>d) <+>
  (m<*>d<*>k<*>f) <+> (n<*>h<*>k<*>a) <+> (o<*>l<*>f<*>a) <+>
  (u<*>i<*>c<*>f) <+> (u<*>j<*>g<*>a) <+> (u<*>k<*>e<*>b) <+>
  (q<*>s))
  <=>
  ((m<*>b<*>h<*>k) <+> (m<*>c<*>l<*>f) <+> (n<*>e<*>d<*>k) <+>
  (n<*>g<*>l<*>a) <+> (o<*>i<*>d<*>f) <+> (o<*>j<*>h<*>a) <+>
  (m<*>d<*>j<*>g) <+> (n<*>h<*>i<*>c) <+> (o<*>l<*>e<*>b) <+> 
  (u<*>i<*>b<*>g) <+> (u<*>j<*>e<*>c) <+> (u<*>k<*>f<*>a))
 in
 factor_quad p q <&> factor_quad r s <&> zero <&> one <&> two <&> three
;;

 (* restrict number of ev with value 1 *)
let triple_add (a,b,c) (d,e,f) = (a<+>d,b<+>e,c<+>f);;
let triple_max (a,b,c) = Logic.max (Logic.max a b) c;;
let discr4 p q = (p<*>p) <-> ((of_int 4)<*>q);;

(*returns (a,b,c) where 
 a = m_\lambda with \lambda = 1
 b = m_\lambda with \lambda = -1
 c = m_\lambda with \lambda = c+di and |c+di| = 1
*)
(*case compl is an overapproximations*)
let ew2_1 p q = 
 let d = discr4 p q in
 let z = Logic.zero and one = Logic.one and two = of_int 2 in
 let it f x = Logic.ite f x z in
 let reals2 = Triple.map (it (d <=> z)) (it (p <=> (of_int ~-2)) two,it (p <=> two) two,z) in
 let reals1 = Triple.map (it (d <>> z)) (it (p <<=> z) one, it(p <>=> z) one, z) in
 let compl  = Triple.map (it (d <<> z)) (z,z,one) in
 triple_add (triple_add reals1 reals2) compl
;;

let ew1_1 p = (*if p = 1 then \lambda = 1*)
 (ito (p <=> Logic.one), ito (p <=> Logic.minus_one), Logic.zero)
;;

let max_mul_ew1 ls = 
 let z = Logic.zero in
 let (a,b,c) = List.foldr triple_add (z,z,z) ls in
 Logic.max (Logic.max a b) c
;;
 
let degree d p q r s = match d with
 | 1 -> Logic.one
 | 2 -> max_mul_ew1 [ew2_1 p q]
 | 3 -> max_mul_ew1 [ew2_1 p q; ew1_1 r]
 | 4 -> max_mul_ew1 [ew2_1 p q; ew2_1 r s]
 | n -> Logic.constant (Number.of_int n)
;;

let factor fs = max_matrix fs >>= fun m ->
 let sint = Logic.int 3 in
 let spec = {sint with Logic.rat = !(flags.rat)} in (*rational factorisation?*)
 fresh_arith_spec spec >>= fun p -> fresh_arith_spec spec >>= fun q ->
 fresh_arith_spec spec >>= fun r -> fresh_arith_spec spec >>= fun s ->
 let f = 
  match !(flags.dim) with
   | 1 -> factor_1 p m
   | 2 -> factor_2 p q m 
   | 3 -> factor_3 p q r m
   | 4 -> factor_4 p q r s m
   | _ -> failwith "matrix -factor: wrong dimension"
 in
 let aux = if !(flags.bound) = 0 then Logic.top 
           else (degree !(flags.dim) p q r s <<=> (of_int !(flags.bound))) in
 Made.return (f <&> aux)
;;

(*minimal polynomial criterion*)
let annihilates cs a = 
 let rec prod a2 a i = function
  | [] -> i
  | [c;r] -> M.add (M.scale c a) (M.scale Logic.minus_one (M.scale r i))
  | c::p::q::cs -> 
   M.mul (M.add (M.add (M.scale c a2) (M.scale p a)) (M.scale q i)) (prod a2 a i cs)
 in
 let a2 = M.mul a a in
 let i = M.identity (M.rows a) in
 let zero = M.zero (M.rows a) (M.columns a) in
 equal_matrix (prod a2 a i cs) zero
;;

(*if [c = 0] then constraints hold for free*)
let rec bound_roots = function
 | [] -> Logic.top
 | [c;r] -> (*(c <=> Logic.one) <->>*) (factor_lin r)
 | c::p::q::cs -> (*(c <=> Logic.one) <->>*) (factor_quad p q <&> bound_roots cs)
;;

(*cancel some factors by 0/1 variable c*)
let rec cancel fresh = function
 | [] -> 
  Made.return []
 | [r] -> fresh () >>= fun c -> 
  Made.return [c;((c<*>r) <+> c) <-> Logic.one]
 | p::q::cs -> 
  fresh () >>= fun c ->
  cancel fresh cs >>= fun ds ->
  Made.return ([c;c<*>p;((c<*>q)<+>Logic.one)<->c]@ds)
;;

let generate_apc _ = get >>= fun c ->
 let sint = Logic.int 3 in
 let spec = {sint with Logic.rat = !(flags.rat)} in (*rational factorisation?*)
 let fresh = fun _ -> (fresh_arith_spec spec) in
 let spec01 = Logic.nat 1 in
 let fresh01 = fun _ -> (fresh_arith_spec spec01) in
 let deg = if !(flags.mpd) = 0 then !(flags.dim) else !(flags.mpd) in
 Made.sequence (List.gen fresh deg) >>= fun cs ->
 cancel fresh01 cs >>= fun ds ->
 c.ap := ds;
 Made.return !(c.ap)
;;

let get_apc _ = get >>= fun c -> Made.return !(c.ap);;

(*count (1,-1,complex)*)
let count_1 r = (*if r = 1 then \lambda = 1*)
 (ito (r <=> Logic.one),
  ito (r <=> Logic.minus_one),
  Logic.zero)
;;
let count_2 p q = 
 let d = (p<*>p) <-> (Logic.of_int 4<*>q) in
 let m11 = (*multiplicity of -1 and +1 depending on d*)
  Logic.ite (d <=> Logic.zero) (Logic.of_int 2) 
  (Logic.ite (d <>> Logic.zero) Logic.one Logic.zero) in
 let c11 = (*multiplicity of complex \lambda depending on d*)
  Logic.ite (d <<> Logic.zero) Logic.one Logic.zero in
 (m11 <*> ito ((p<+>q<+>Logic.one)<=> Logic.zero),
  m11 <*> ito (p<=>(q<+>Logic.one)),
  c11 <*> ito (q<=>Logic.one)
 )
;;
  
let bound_degree cs = 
 let rec count = function 
  | [] -> (Logic.zero,Logic.zero,Logic.zero)
  (*[c] can be ignored since [c=0] does not give [|\lambda| = 1]*)
  | _::r::[] -> count_1 r 
  | _::p::q::cs -> triple_add (count_2 p q) (count cs)
 in
 let degree = triple_max (count cs) in
 if !(flags.bound) = 0 then Logic.top else degree <<=> Logic.of_int !(flags.bound)
;;

(*annihilating => monic, since not monic => p(x) = 1 contradicts p(x) = 0*)
let rec monic = function
 | [] -> Logic.top
 | [c;_] -> (c <=> Logic.one)
 | c::_::_::cs -> (c <=> Logic.one) <|> (monic cs)
;;

let rec sum = function
 | [] -> Logic.zero
 | [c;_] -> c
 | c::_::_::cs -> c <+> (sum cs)
;;

let minpol fs = max_matrix fs >>= fun m ->
 generate_apc () >>= fun cs ->
 Made.return (monic cs <&> annihilates cs m <&> bound_roots cs <&> bound_degree cs)
;;

(*jsr encoding*)
module BM = Matrix.Make(BoolCoefficient);;
module CM = Matrix.Make(CountCoefficient);;

let make_g2 d fs = 
 matrices fs >>= fun ms ->
 let make_ij k l = 
  let i = k / d in
  let i' = k mod d in
  let j = l / d in
  let j' = l mod d in
  let z = Logic.zero in
  (Logic.big_or (List.map (fun m -> (M.get i j m <>> z) <&> (M.get i' j' m <>> z)) ms))
 in
 Made.return (BM.makeij (d*d) (d*d) make_ij)
;;

let mem m c = 
 Logic.big_and 
  (List.map2 BoolCoefficient.geq (BM.to_list c) (BM.to_list m))
;;

let make_bin_matrix r c = 
 Made.sequence (List.gen (const fresh_bool) (r*c)) >>= fun es ->
 Made.return (BM.of_list r c es)
;;

(*an overapproximation of the transitive closure *)
let tca dim m =
 make_bin_matrix dim dim >>= fun c ->
 Made.return (c,mem m c <&> mem (BM.mul c c) c)
;;

(*
 this is a stronger condition than 
 (c_ij > 0 -> m_ij > 0) & (c_ij > 1 -> m_ij > 1)
 but should be equivalent for weight-2-cycle-free graphs
*)
let mem' m c = 
 Logic.big_and
  (List.map2 CountCoefficient.geq (CM.to_list c) (CM.to_list m))
;;

let make_count_matrix r c = 
 Made.sequence (List.gen (const fresh_arith) (r*c)) >>= fun es ->
 Made.return (CM.of_list r c es)
;;

let tca' dim m =
 make_count_matrix dim dim >>= fun c ->
 let m' = CM.of_list dim dim (M.to_list m) in
 Made.return (c,mem' m' c <&> mem' (CM.mul c c) c)
;;

let cond1 dim m = 
 (*all weights <= 1 -> no cycle with edge of weight >= 2*)
 (*let no_cycle = Logic.big_and (List.map (fun e -> e <<=> Logic.one) (M.to_list m)) in*)
 tca' dim m >>= fun (c,aux) ->
 let no_cycle = Logic.big_and (List.gen (fun i -> CM.get i i c <<=> Logic.one) dim) in
 Made.return (no_cycle <&> aux)
;;

let diff_times dim = 
 List.filter (fun (x,y) -> x <> y) (List.square (List.range 0 dim))
;;

let cycle_d dim i tc = 
 Logic.big_or (List.map (fun (p,q) -> 
  let k = i*dim+i and j = p*dim+q in
  (BM.get k j tc <&> BM.get j k tc))
  (diff_times dim))
;;

let cycle dim tc =
 Logic.big_or (List.gen (fun i -> cycle_d dim i tc) dim)
;;

let cond2 dim g2 = 
 let d = BM.rows g2 in
 tca d g2 >>= fun (tc,aux) ->
 let no_cycle = Logic.neg (cycle dim tc) in
 Made.return (no_cycle <&> aux)
;;

let scc c i j = BM.get i j c <&> BM.get j i c;;
let diff ss i j = Logic.neg (List.nth ss i <=> List.nth ss j);;
let b_ij c ss i j = 
 if i = j then Logic.top else Logic.neg (scc c i j) <->> diff ss i j
;;

let bound dim c ss = 
 let aux = List.gen (fun i -> 
  Logic.big_and (List.gen (fun j -> b_ij c ss i j) dim))
  dim
 in
 let bound = List.gen (fun i -> List.nth ss i <<> Logic.of_int !(flags.bound)) dim in
 Logic.big_and (bound @ aux)
;;

let geq x y = x <->> (y <>> Logic.zero);;

let mem'' m c =
 Logic.big_and
  (List.map2 geq (BM.to_list c) (M.to_list m))
;;

(*corollary 3.5*)
let bound_jsr dim m =
  make_bin_matrix dim dim >>= fun c ->
  let aux = mem'' m c <&> mem (BM.mul c c) c in
  let spec = Logic.nat !(flags.bound) in
  Made.sequence (List.gen (fun _ -> fresh_arith_spec spec) dim) >>= fun ss ->
  let bound = bound dim c ss in
  Made.return (bound <&> aux)
;;

(*theorem 3.3*)
let make_g3 d fs = 
 matrices fs >>= fun ms ->
 let d2 = d*d in
 let make_ij l m = 
  let i = l / d2 in
  let j = (l / d) mod d in
  let k = l mod d in
  let i' = m / d2 in
  let j' = (m / d) mod d in
  let k' = m mod d in
  let z = Logic.zero in
  (Logic.big_or (List.map (fun m -> 
   (M.get i i' m <>> z) <&> (M.get j j' m <>> z) <&> (M.get k k' m <>> z)) ms))
 in
 Made.return (BM.makeij (d*d*d) (d*d*d) make_ij)
;;


let g3l i j = get >>= fun c -> cache_m c.g3l (fun _ -> 
 let spec = Logic.nat !(flags.dim) in
 fresh_arith_spec spec) (i,j)
;;

let triple g3 i j = BM.get i i g3 <&> BM.get i j g3 <&> BM.get j j g3;;

let gen g3 i j k = 
  if i <> j & j <> k & (i < j || (i = j && j < k)) then
  Made.return (triple g3 i j <&> triple g3 j k) $->$ (g3l i j $=$ g3l j k)
  else
   Made.return Logic.top
;;
let ij d g3 i j = 
 Made.sequence (List.gen (gen g3 i j) d) >>= fun ijk ->
 g3l i j >>= fun g3lij ->
 Made.return ((triple g3 i j <->> (((g3lij <>> Logic.zero)) <&> (g3lij
 <<=> Logic.of_int !(flags.bound)))) <&> Logic.big_and ijk)
;;
let i d g3  i   = Made.liftM Logic.big_and (Made.sequence (List.gen (ij d g3 i) d));;

let count d c = 
 Made.liftM big_add (Made.sequence (List.gen (fun i ->
  Made.liftM big_add (Made.sequence 
   (List.gen (fun j -> g3l i j >>= fun gij -> Made.return (ito (gij <=> c))) d)
 )) d
 ))
;;

let b_ext d g3 = 
 Made.sequence (List.gen (i d g3) d) >>= fun aux ->
 Made.sequence (List.gen (fun c -> 
  count d (Logic.of_int c) >>= fun count ->
  Made.return (count <<=> Logic.of_int !(flags.bound))) d) >>= fun count ->
 Made.return (Logic.big_and (aux@count))
;;

let bound_exact dim fs = 
 make_g3 dim fs >>= fun g3 ->
 let d = BM.rows g3 in
 tca d g3 >>= fun (tc,aux) ->
 b_ext dim tc >>= fun bound -> 
 Made.return (bound<&> aux)
;;

let condb d fs mm = 
 if !(flags.bound) = 0 then Made.return Logic.top
 else if !(flags.jsre) then bound_exact d fs
 else bound_jsr d mm
;;

let jsr fs = 
 max_matrix fs >>= fun mm ->
 let d = M.rows mm in
 make_g2 d fs >>= fun g2 ->
 cond1 d mm $&$ cond2 d g2 $&$ condb d fs mm
;;

(*reachability criterion*)
let mul_1 m = 
 map_and diagonal_ok ([m])
;;

let mul_2 m = 
 let m2 = M.mul m m in
 map_and diagonal_ok ([m;m2])
;;

let mul_3 m = 
 let m2 = M.mul m m in
 let m3 = M.mul m2 m in
 map_and diagonal_ok ([m;m2;m3])
;;

let mul_4 m = 
 let m2 = M.mul m m in
 let m3 = M.mul m2 m in
 let m4 = M.mul m2 m2 in
 let m5 = M.mul m4 m in
 map_and diagonal_ok ([m;m2;m3;m4;m5])
;;

let mul_5 m = 
 let m2 = M.mul m m in
 let m3 = M.mul m2 m in
 let m4 = M.mul m2 m2 in
 let m5 = M.mul m4 m in
 let m6 = M.mul m3 m3 in
 let m7 = M.mul m6 m in
 map_and diagonal_ok ([m;m2;m3;m4;m5;m6;m7])
;;

let mul_6 m = 
 let m2 = M.mul m m in
 let m3 = M.mul m2 m in
 let m4 = M.mul m2 m2 in
 let m5 = M.mul m4 m in
 let m6 = M.mul m3 m3 in
 let m7 = M.mul m6 m in
 let m8 = M.mul m4 m4 in
 let m9 = M.mul m8 m in
 map_and diagonal_ok ([m;m2;m3;m4;m5;m6;m7;m8;m9])
;;

let mul fs = max_matrix fs >>= fun m -> match !(flags.dim) with
 | 1 -> mul_1 m
 | 2 -> mul_2 m
 | 3 -> mul_3 m
 | 4 -> mul_4 m
 | 5 -> mul_5 m
 | 6 -> mul_6 m
 | _ -> failwith "matrix -mul: too large dimension"

let triangular_matrix m = 
 let r = M.rows m and c = M.columns m in
 gen_and (fun k -> 
  let i,j = k / r, k mod c in
  Made.return (
   if i = j then (M.get i j m <<=> Logic.one) 
   else if i > j then (M.get i j m <=> Logic.zero)
   else Logic.top
  )) (r*c)
;;

let gp = ref (M.zero 1 1);;
let gpi = ref (M.zero 1 1);;

(*diagonalizable criterion*)
let diagonalizable fs = max_matrix fs >>= fun m ->
 let d = !(flags.dim) in
 let arith = fresh_arith_spec (Logic.nat 1) in
 make_matrix ~fresh:arith false false 0 d d >>= fun p ->
 make_matrix ~fresh:arith false false 0 d d >>= fun pi ->
 gp := p; gpi := pi;
  (Made.return (
  equal_matrix (M.mul p pi) (M.identity d) <&>
  equal_matrix (M.mul pi p) (M.identity d)) $&$
  triangular_matrix (M.mul (M.mul p m) pi)
  )
 ;;
 
(* complexity encodings end *)

let encode_gt s w = get >>= fun c -> 
 let s = if !(flags.dp) || poly_complexity flags || !(flags.dir) then s
         else List.rev_append s w in
 if !(flags.inc) = None then 
  let op = (if !(flags.dir) then Logic.big_and else Logic.big_or) in
  map_op op greater_rule s
 else match Option.the !(flags.inc) with
  | A -> minimal_cycle s
  | B -> almost_minimal_cycle s
  | C -> encode_compress (label_graph c.graph)
  | E -> encode_direct_edge (label_graph c.graph)
  | N -> encode_direct_node (label_graph c.graph)
;;

let sum m = big_add (M.to_list m);;

let sum_f n f = arity f >>= fun a ->
 let c = Logic.constant (Number.of_int n) in
 Made.sequence (List.gen (coefficient f) a) >>= fun cs ->
 Made.return (Logic.big_and (List.map (fun ci -> sum ci <<=> c) cs)) >>= fun aux ->
 Made.return (Logic.obits (Int.bits n) aux)
;;

let sum n fs = 
 Made.liftM Logic.big_and (Made.sequence (List.map (sum_f n) fs)) >>= fun c ->
 Made.return (Logic.obits 10 c);
;;

(*auxiliary constraints that may help find solution*)
let diagonal_m m = 
 Made.return (Logic.big_and (
  List.gen (fun i -> M.get i i m <<=> Logic.one) !(flags.dim)
 ));;

let diagonal2_m m = 
 Made.return (Logic.big_and (List.gen (fun i ->
  Logic.big_and (List.gen (fun j -> if i < j then
   (M.get i j m <<=> Logic.one) <|> (M.get j i m <<=> Logic.one) <&>
    (M.get i j m <*> M.get j i m <<=> Logic.one)
   else Logic.top
   ) !(flags.dim))
  ) !(flags.dim)))
;;

let poly_complexity_aux fs = 
 (if !(flags.jsr) then matrices fs else (max_matrix fs >>= fun m -> return [m]))  
  >>= fun ms ->
 map_and diagonal_m ms $&$
 map_and diagonal2_m ms
;;

let monf f = 
 coefficients f >>= fun cs -> 
 return (Logic.big_and (List.map (fun ci -> M.get 0 0 ci <>=> Logic.one) cs))
;;

let desired2_rule rule = 
 let f = Option.the (Term.root (Rule.lhs rule)) in
 monf f >>= fun mf ->
 ((liftM Logic.neg) (monf f)) $->$ greater_rule rule
;;

let desired2 trs = map_and desired2_rule (Trs.to_list trs);;

let encode2 strict weak = get >>= fun c ->
 let (s, w) = Pair.map Trs.to_list (strict, weak) in
 let fs = Trs.funs (Trs.union strict weak) in
 encode_geq s w $&$
 encode_gt s w $&$
 (if !(flags.sum) = 0 then return Logic.top else sum !(flags.sum) fs) $&$
 (if !(flags.dp) then return Logic.top else mon fs) $&$
 (if !(flags.tri) then triangle fs $&$ (
  if !(flags.bound) <> 0 then count_ones !(flags.bound) fs 
  else return Logic.top)
 else return Logic.top) $&$
 liftM (if !(flags.ob2) = 0 then id else Logic.obits !(flags.ob2))
  (
  (if !(flags.explicit) then explicit fs else return Logic.top) $&$
  (if !(flags.implicit) then implicit fs else return Logic.top) $&$
  (if !(flags.factor) then factor fs else return Logic.top) $&$
  (if !(flags.minpol) then minpol fs else return Logic.top) $&$
  (if !(flags.jsr) then jsr fs else return Logic.top) $&$
  (if !(flags.mul) then mul fs else return Logic.top) $&$
  (if !(flags.diag) then diagonalizable fs else return Logic.top)
 ) $&$
 (if !(flags.str) && (Trs.is_duplicating strict) then return Logic.bot else return Logic.top) $&$
 (if !(flags.ds2) then desired2 (Trs.union strict weak) else return Logic.top)
;;

let max_matrix_constraints _ = get >>= fun c ->
 match !(c.max_matrix) with
  | None -> Made.return Logic.top
  | Some (_,c) -> Made.return c
;;

let get_side_constraints strict weak =
 let fs = Trs.funs (Trs.union strict weak) in
 (if (poly_complexity flags) then poly_complexity_aux fs else return Logic.top) $&$
 max_matrix_constraints ()
;;

let encode strict weak = 
 encode2 strict weak $&$ get_side_constraints strict weak
;;

let eval_matrix ass m = m >>= fun m -> 
 let r, c = M.rows m, M.columns m in
 Made.sequence 
  (List.map (fun (i,j) -> lift (Logic.eval_a (M.get i j m) ass))
  (List.product (List.range 0 r) (List.range 0 c))) >>= fun ms ->
 return (NM.of_list r c ms);;

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

let decode_rule ass rule = liftM not (eval_p (greater_rule rule) ass);;

let decode_monf ass f = 
 get_interpretation ass f >>= fun (_,coeffs,_) ->
 if List.for_all (fun c -> Number.ge (NM.get 0 0 c) Number.one) coeffs then return []
 else 
  arity f >>= fun n ->
  get_fun 0 >>= fun c ->
  get_vars n >>= fun xs ->
  return [Rule.of_terms (Term.make_fun c []) (Term.make_fun f (List.map Term.make_var xs))]
;;

(*TODO: do not add if already present*)
let decode_mon ass fs = 
 Made.map (decode_monf ass) fs >>= fun rs -> 
 return (Trs.of_list (List.concat rs))
;;
 

let decode_trs ass trs = Made.filter (decode_rule ass) (Trs.to_list trs) >>= (return <.> Trs.of_list);;

let decode_weak ass w = 
 if !(flags.dp) || poly_complexity flags then return w else decode_trs ass w;;

(*
let label_dh trs n s = 
 let m = if Trs.mem (Rewrite.step_get_rule s) trs then n else n-1 in
 let s = Rewrite.step_add_label ~left:!(flags.left) s n in
 (m,s)
;;

let decode_ldh ass p = 
 let (s,w) = Problem.get_sw p in
 decode_trs ass s >>= fun s ->
 decode_weak ass w >>= fun w ->
 let f = label_dh (Trs.union s w) in
 let cds = List.map (Diagram.label f) (Problem.get_cds p) in
 return (Problem.set_cds cds p)
;;
*)

let label_starm left d i (_, s) = 
 Term.spine (Rewrite.step_get_term s) (Rewrite.step_get_pos s) >>>>= fun u ->
 let ti = eval_const d i u in
 let l = Number.to_int (NM.get 0 0 (NMono.coefficient (NP.constant_part ti))) in
 let s = Rewrite.step_add_label ~left:left s l in
 Monad.return (l,s)
;;

let decode_lstar ass p = get >>= fun c -> 
 let (s,w) = Problem.get_sw p in
 decode_intp ass (Trs.union s w) >>= fun i ->
 let f = label_starm !(flags.left) !(flags.dim) i in
 lift_monad (Monad.freeze f) >>= fun f ->
 return (Problem.label_cds (fun i n -> f (i, n)) (~-1) p)
;;
 
let decode ass p = get >>= fun c -> 
 let (strict,weak) = Problem.get_sw p in
 (if !(flags.inc) = None then (
  decode_trs ass strict >>= fun s ->
  decode_weak ass weak >>= fun w0 ->
  (if !(flags.ds2) then decode_mon ass (Trs.funs (Trs.union strict weak)) else return Trs.empty) >>= fun w1 -> (*hydra*)
  return (Problem.set_sw s (Trs.union w0 w1) p)
 ) else match Option.the !(flags.inc) with
   | A (* fallthrough *)
   | B -> return (Problem.set_dps Trs.empty p)
   | C -> decode_compress_edge ass p
   | E -> decode_direct_edge ass p
   | N -> decode_direct_node ass p
 ) >>= fun p ->
 if !(flags.cp) then (
  let s',w' = Problem.get_sw p in
  let t = Trs.diff strict s' in 
  return (Problem.set_sw s' (Trs.union t weak) p)
 ) else return p >>= fun p ->
 (* if !(flags.ldh) then decode_ldh ass p else return p >>= fun p -> *)
 if !(flags.lstar) then decode_lstar ass p else return p >>= fun p ->
 return p
;;

let decode_ur_rule ass rule = eval_p (u (Rule.lhs rule)) ass;;

let decode_trs_ur ass w =
 Made.filter (decode_ur_rule ass) (Trs.to_list w) >>= (return <.> Trs.of_list)
;;

let decode_ur ass w = get >>= fun c ->
 if !(flags.ur) then (decode_trs_ur ass w >>= (return <.> Option.some))
 else (return None)
;;

let decode_ap ass = 
 if !(flags.minpol) then 
  get_apc () >>= fun cs ->
  Made.map (fun ci -> eval_a (Made.return ci) ass) cs >>= fun cx ->
  Made.return (Some cx)
 else
  Made.return None
;;

let decode_cpx ass = 
 Made.return 
 (if !(flags.bound) > 0 then (
  if !(flags.jsr) then Some !(flags.bound)
  else Some !(flags.dim)
 )
 else
 None
 )
;;

let print_formula fs phi = get >>= fun c -> 
 let fprintf_formula = 
  if !(flags.p) then Logic.fprintf_smt 
  else if !(flags.p2) then Logic.fprintf_smt2
  else failwith (code ^ ".flag p or p2 expected")
  in
 let logic = if !(flags.rat) > 1 || !(flags.real) then "QF_NRA" else "QF_NIA" in
 let source = List.join id " " ("ttt2"::code::fs) in
 Format.fprintf Format.std_formatter "@[%a@]@\n" 
  (fun ppt -> fprintf_formula ~logic:logic ~source:source ppt) phi;
 return (get_state c,None)
;;

let solve s fs p = 
 let configurate s = F.printf "%s@\n%!" s; flags.help := true in
 (try init (); Arg.parsex code spec fs with Arg.Bad s -> configurate s);
 if !(flags.help) then (Arg.usage spec ("Options for "^code^":"); exit 0);
 let c = context s p in
 let (s,w) = Problem.get_sw p in
 Logic.run ~dbits:!(flags.db) ~obits:!(flags.ob) (
  Made.run c (encode s w >>= fun phi ->
   if Trs.is_empty s && not !(flags.strict_empty) then
    get >>= fun c ->
    return (get_state c, None)
   else if !(flags.p) || !(flags.p2) then print_formula fs phi
   else
   Made.lift (Logic.solve ~solver:!(flags.solver) phi) >>= function
    | None -> return (get_state c,None)
    | Some ass -> 
     decode ass p >>= fun p' -> decode_ur ass w >>= fun ur ->
     decode_intp ass (Trs.union s w) >>= fun i ->
     let dim = !(flags.dim) and dir = !(flags.dir) in
     let dp = !(flags.dp) and cp = !(flags.cp) in
     let o = !(flags.overlay) in
     let pol = poly_complexity flags in
     let dom = Dom.domain_of_rat_real !(flags.rat) !(flags.real) in
     decode_ap ass >>= fun ap ->
     decode_cpx ass >>= fun cpx ->
     let proof = 
      (Some (make dim dir dom dp cp cpx !(flags.tmp) !(flags.tri) i p p' ur o
      pol ap !(flags.dimbound)))
     in
     get >>= fun c ->
     return (get_state c,proof)))
   
;;

(* compute complexity Bounds *)

let incnz n = if Number.eq n Number.zero then 0 else 1;;

let one_if_one n = if Number.eq n Number.one then Number.one else Number.zero;;

let overlay d i =
 let m = max_interpretation d i and xs = List.range 0 d in
 List.foldl (fun acc i -> incnz (one_if_one (NM.get i i m)) + acc) 0 xs
;;

(*TODO: check if M.of_list (M.to_list m) = m *)
let map_matrix f m = 
 let r = NM.rows m and c = NM.columns m in
 let ms = NM.to_list m in
 M.of_list r c (List.map f ms)
;;

let factor p q r s d m = 
 Logic.return (
  match d with
  | 1 -> factor_1 p m
  | 2 -> factor_2 p q m
  | 3 -> factor_3 p q r m
  | 4 -> factor_4 p q r s m
  | _ -> Logic.top (*return dimension as it is*)
 )
;;

let complexity p =
 let d = p.dimension and i = p.interpretation and apc = p.apc in
 match apc with
  | None -> 
  let m = map_matrix Logic.constant (max_interpretation d i) in
  let sint = Logic.int 10 in
  let spec = {sint with Logic.rat = 1} in
   Logic.run ~dbits:0 ~obits:10 (
   Logic.fresh_arith spec >>>= fun p -> Logic.fresh_arith spec >>>= fun q ->
   Logic.fresh_arith spec >>>= fun r -> Logic.fresh_arith spec >>>= fun s ->
    (factor p q r s d m >>>= fun phi ->
      (Logic.solve phi) >>>= function
      | None -> Logic.return d
      | Some ass -> Logic.eval_a (degree d p q r s) ass >>>= fun d ->
       Logic.return (int_of_string (Number.to_string d))
   ))
   | Some cs -> degree_from_ap cs
;;

let complexity c p =
 let ip = get_ip p in
 let cp = (Problem.is_sp ip && p.direct) || (Problem.is_cp ip && p.complexity) in
 if cp && p.monotone && p.poly then
  let b1 = complexity p in 
  let b2 = if p.triangle then overlay p.dimension p.interpretation else p.dimension in
  let b3 = match p.cpx with | Some d -> d | None -> p.dimension in
  let b = if p.dimbnd then p.dimension else min (min b1 b2) b3 in
  (* if p.triangle then *)
             (* if p.ov then overlay p.dimension p.interpretation else
             p.dimension *)
          (* else (*if p.poly then*) *)
             (* complexity p *)
  (* in *)
  Co.add c (Co.poly (Some b))
 else Co.mul c Co.other
;;

(* wrap into state monad *)
let (>>=) = Monad.(>>=);;
let (>>) = Monad.(>>);;

let solve fs p = 
 if Problem.is_sp p || Problem.is_rp p || Problem.is_dp p ||
   Problem.is_cp p || Problem.is_ddp p || Problem.is_auxp p then
  Monad.get >>= fun s -> 
  let s,proof = solve s fs p in
  Monad.set s >> 
  Monad.return proof
 else Monad.return None
;;
