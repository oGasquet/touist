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
module XO = XmlOutput;;

(*** TYPES ********************************************************************)

type t = {
 degree : int;
 direct : bool; 
 monotone : bool;
 triangle : bool;
 interpretation : (string * Number.t list) list;
 input : Problem.t;
 output :Problem.t;
 usable_rules : Trs.t option;
};;

type flags = {
 db : int ref;
 deg : int ref;
 dir : bool ref;
 dp : bool ref;
 help : bool ref;
 min : int ref;
 neg : bool ref;
 o  : bool ref;
 ob : int ref;
 p : bool ref;
 p2 : bool ref;
 rat : int ref;
 real : bool ref;
 st : bool ref;
 tri : bool ref;
 ur : bool ref;
 w  : bool ref; (*experimental*)
};;

type context = {
 arith              : Logic.arith;
 usable             : (Fun.t,Logic.p) Hashtbl.t;
 coefficients       : (Fun.t, Logic.a list) Hashtbl.t;
 gt_encodings       : (Rule.t,Logic.p) Hashtbl.t;
 geq_encodings      : (Rule.t,Logic.p) Hashtbl.t;
 state              : Sig.t;
 subterm_encodings  : (Term.t,Logic.a list) Hashtbl.t;
 orient             : bool;
};;

(*** GLOBALS ******************************************************************)
let code = "ordinal";;
let name = "Ordinal Interpretation Processor";;
let comment = "Applies ordinal interpretations."
let keywords = ["ordinal interpretation";"linear interpretation";"termination"];;

let flags = {
 db = ref max_int;
 deg = ref 1;
 dir = ref false;
 dp = ref false;
 help = ref false;
 min = ref 1;
 neg = ref false;
 o   = ref false;
 ob = ref max_int;
 p = ref false;
 p2 = ref false;
 rat = ref 1;
 real = ref false;
 st = ref false;
 tri = ref false;
 ur = ref false;
 w = ref false; (*experimental*)
};;

let spec =
 let spec = [
  ("-degree",Arg.Set_int flags.deg,"Degree of ordinal (std: 1).");
  ("-direct",Arg.Set flags.dir,"Try to finish termination proof.");
  ("-dp",Arg.Set flags.dp,
   "Allows non-monotone interpretations, i.e., `0' as coefficient.");
  ("--help",Arg.Set flags.help,"Prints information about flags.");
  ("-help",Arg.Set flags.help,"Prints information about flags.");
  ("-h",Arg.Set flags.help,"Prints information about flags.");
  ("-ib",Arg.Int ((:=) flags.min <.> Int.bit_max),
   "Defines the number of bits used to represent matrix entries (same as \
   `-min' but in bits).");
  ("-max",Arg.Int ((:=) flags.ob <.> Int.bits),
   "Defines the maximum number that can appear as intermediate result.");
  ("-min",Arg.Set_int flags.min,
   "Defines the minimum matrix entry that should be representable.");
  (*
  ("-neg",Arg.Set flags.neg,
   "Allow negative numbers (only for non-linear interpretations).");
  *)
  ("-ob",Arg.Set_int flags.ob,
   "Defines the number of bits used to represent intermediate results \
    (same as `-max' but in bits)");
  ("-p",Arg.Set flags.p,
   "Print encoding in SMT-LIB format v1.2 and fail");
  ("-p2",Arg.Set flags.p2,
   "Print encoding in SMT-LIB format v2.0 and fail");
  ("-st",Arg.Set flags.st,
   "Demand weak subterm property");
  ] in
 Arg.alignx 80 spec
;;

let help = (comment,keywords,List.map Triple.drop_snd spec);;

(*** MODULES (part 2) *********************************************************)
module Statex = struct type t = context end;;
module Made = Util.Monad.Transformer.State (Statex) (Logic.Monad);;
open Made;;

(*** FUNCTIONS ****************************************************************)
let init _ =
 flags.db := max_int;
 flags.deg := 1;
 flags.dir := false;
 flags.dp := false;
 flags.help := false;
 flags.min := 1;
 flags.neg := false;
 flags.ob := max_int;
 flags.rat := 1;
 flags.real := false;
 flags.st := false;
 flags.tri := false;
 flags.ur := false;
;;

(* Constructors and Destructors *)
let make deg dir dp tri i input output ur = {
 degree = deg;
 direct = dir;
 monotone = not dp;
 triangle = tri;
 interpretation = i;
 input = input;
 output = output;
 usable_rules = ur;
};;

let get_ip p = p.input;;
let get_op p = p.output;;

(* Complexity Bounds *)
let complexity c p = Co.other;;

(* Compare Functions *)
let equal p q =
 Problem.equal p.input q.input && Problem.equal p.output q.output
;;

(* Printers *)
let (>>=) = Monad.(>>=);;

let fprintf_elt i fmt c =
 if i = 0 then Number.fprintf fmt c
 else Format.fprintf fmt "w^%d %a" i Number.fprintf c
;;

let fprintf_intp_p fmt (f,c::cs) = 
 F.fprintf fmt "%s(x) =  %ax + " f Number.fprintf c;
 let n = List.length cs -1 in
 List.fprintfi (fun i c -> fprintf_elt (n-i) c) " + " fmt cs
;;

let fprintf_intp fmt fs = List.fprintf fprintf_intp_p "@\n" fmt fs;;

let fprintf fs fmt p  = 
 F.fprintf fmt "@[<1>%s:@\ndegree : %i" name p.degree;
 F.fprintf fmt "@\n@[<1>interpretation:@\n%a" fprintf_intp p.interpretation; 
 (**)
 (* F.fprintf fmt "@]@\n@[<1>orientation:@\n"; *)
 (* fprintf_orient 1 p.interpretation fmt p.input >>= fun _ -> *)
 (**)
 F.fprintf fmt "@]@\n@[<1>problem:@\n";
 Problem.fprintfm fmt p.output >>= fun _ ->
 F.fprintf fmt "@]@\n"; List.hd fs fmt >>= fun _ ->
 Monad.return (F.fprintf fmt "@]")
;;

let fprintfx fs p = failwith "XML not supported" ;;


(* Processor *)
(* administrative functions *)
let (>>=) = Made.(>>=);;

let count f t = List.length (Term.fun_pos f t);;
let count_rule p f r = let lc,rc = Rule.map (count f) r in p lc || p rc;;
let rec parallel = function
 | [] -> true
 | p::ps -> List.for_all (Position.are_parallel p) ps && parallel ps
;;
let nested f t = not (parallel (Term.fun_pos f t));;
let nested_rule f r = let lc,rc = Rule.map (nested f) r in lc || rc;;

let print state f = 
 let _ = Sig.fprintf_fun Format.std_formatter f state in
 let _ = Format.printf " -> ari:%d@\n" (Sig.find_ari f state) in
 ()
;;

let context state problem =
 let (s,_) = Pair.map Trs.to_list (Problem.get_sw problem) in
 let arith = {
  Logic.min = Int64.of_int !(flags.min);
  neg       = false;
  rat       = !(flags.rat);
  real      = !(flags.real);
  minf      = false}
 in
 {arith              = arith;
  usable             = Hashtbl.create 512;
  coefficients       = Hashtbl.create 512;
  gt_encodings       = Hashtbl.create 512;
  geq_encodings      = Hashtbl.create 512;
  state              = state;
  orient             = !(flags.o);
  subterm_encodings  = Hashtbl.create 512;
 }
;;

let cache_m tbl f k = 
 if Hashtbl.mem tbl k then return (Hashtbl.find tbl k)
 else (f k >>= fun v -> (Hashtbl.add tbl k v; return v))
;;

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
let ($+$) = liftM2 (<<>);;
let eval_a a ass = a >>= fun a -> lift (Logic.eval_a a ass);;
let eval_p p ass = p >>= fun p -> lift (Logic.eval_p p ass);;
let map_op op f ls = sequence (List.map f ls) >>= (return <.> op);;
let mapi_op op f ls = sequence (List.mapi f ls) >>= (return <.> op);;
let gen_op op f n = sequence (List.gen f n) >>= (return <.> op);;
let map_and f = map_op Logic.big_and f;;
let mapi_and f = mapi_op Logic.big_and f;;
let gen_and f = gen_op Logic.big_and f;;
let map_or f = map_op Logic.big_or f;;
let mapi_or f = mapi_op Logic.big_or f;;
let gen_or f = gen_op Logic.big_or f;;

(* state monad interaction *)
let is_dp f = get >>= fun c -> return (Sig.is_dp f c.state);;
let arity f = get >>= fun c -> return (Sig.find_ari f c.state);;
let name f = get >>= fun c -> return (Sig.find_fun_name f c.state);;
let id f = get >>= fun c -> return (fst (Sig.to_string_fun f c.state));;
 
(* encoding starts here *)

let degree () = 
 return !(flags.deg)
;;

let make_coefficient f = 
 degree () >>= fun d ->
 Made.sequence (List.gen (fun _ -> fresh_arith) (d+2))
;;

let coefficients f = get >>= fun c ->
 cache_m c.coefficients make_coefficient f
;;

let rec add acc p0 p1 = match p0,p1 with
 | [],[] -> []
 | c0::p0,c1::p1 -> 
  let acc' = acc <&> (c1 <=> Logic.zero) in
  ((Logic.ite acc c0 Logic.zero) <+> c1)::add acc' p0 p1
;;

let add p0 p1 = add Logic.top p0 p1;;

let rec encode_term t = get >>= fun c ->
 cache_m c.subterm_encodings (etc c) t
and etc c = function
 | Term.Var x -> 
  degree () >>= fun d ->
  return (Logic.one::List.replicate (d+1) Logic.zero)
 | Term.Fun (f, [t]) ->
   encode_term t >>= fun es ->
   coefficients f >>= fun (f'::fs) ->
   let e'::es' = List.map ((<*>) f') es in
   return (e'::add es' fs)
;;

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

let greater_equal_rule rule = get >>= fun c ->
 liftM2 (greater_equal_poly) (encode_term (Rule.lhs rule))
  (encode_term (Rule.rhs rule))
;;

let greater_equal_rule rule = get >>= fun c ->
 cache_m c.geq_encodings (greater_equal_rule) rule
;;

let greater_rule rule = get >>= fun c ->
 liftM2 (greater_poly) (encode_term (Rule.lhs rule))
  (encode_term (Rule.rhs rule))
;;

let greater_rule rule = get >>= fun c ->
 cache_m c.gt_encodings greater_rule rule
;;

let encode_geq s w = map_and greater_equal_rule (s@w);;
let encode_gt s w = get >>= fun c -> 
 let s = if !(flags.dp) || !(flags.tri) || !(flags.dir) then s else List.rev_append s w in
 let op = (if !(flags.dir) then Logic.big_and else Logic.big_or) in
 map_op op greater_rule s
;;


(*weak monotonicity and (weak) simple*)
let wmon_f f = coefficients f >>= fun (c::cs) ->
 return (c <>> Logic.zero)
  (* $&$ map_or (fun c -> return (c <>=> Logic.zero)) cs *)
;;


let wmon fs = map_and wmon_f fs;;

let encode strict weak = get >>= fun c ->
 let (s, w) = Pair.map Trs.to_list (strict, weak) in
 let fs = Trs.funs (Trs.union strict weak) in
 encode_geq s w $&$
 encode_gt s w $&$
 wmon fs $&$
 return Logic.top
;;

let decode_rule ass rule = liftM not (eval_p (greater_rule rule) ass);;

let decode_trs ass trs = 
 Made.filter (decode_rule ass) (Trs.to_list trs) >>= (return <.> Trs.of_list)
;;

let decode_weak ass w = if !(flags.dp) || !(flags.tri) then return w else decode_trs ass w;;

let decode ass p = get >>= fun c -> 
 let (s,w) = Problem.get_sw p in
 liftM3 Problem.set_sw (decode_trs ass s) (decode_weak ass w) (return p)
;;

let get_interpretation_f ass f = name f >>= fun name ->
 coefficients f >>= fun fs ->
 Made.sequence (List.map (fun f -> eval_a (return f) ass) fs) >>= fun cs ->
 return (name,cs)
;;

let get_interpretation ass trs = 
 Made.sequence (List.map (get_interpretation_f ass) (Trs.funs trs))
;;

let print_formula fs phi = get >>= fun c -> 
 let fprintf_formula = 
  if !(flags.p) then Logic.fprintf_smt 
  else if !(flags.p2) then Logic.fprintf_smt2
  else failwith (code ^ ".flag p or p2 expected")
  in
 let logic = if !(flags.rat) > 1 || !(flags.real) then "QF_NRA" else "QF_NIA" in
 let source = List.join Util.id " " ("ttt2"::code::fs) in
 Format.fprintf Format.std_formatter "@[%a@]@\n" 
  (fun ppt -> fprintf_formula ~logic:logic ~source:source ppt) phi;
 Made.return None
;;

let solve s fs p = 
 let configurate s = F.printf "%s@\n%!" s; flags.help := true in
 (try init (); Arg.parsex code spec fs with Arg.Bad s -> configurate s);
 if !(flags.help) then (Arg.usage spec ("Options for "^code^":"); exit 0);
 let c = context s p in
 let (s,w) = Problem.get_sw p in
 Logic.run ~dbits:!(flags.db) ~obits:!(flags.ob) (
  Made.run c (encode s w >>= fun phi ->
   if !(flags.p) || !(flags.p2) then print_formula fs phi
   else
   Made.lift (Logic.solve phi) >>= function
    | None -> return None
    | Some ass -> 
     decode ass p >>= fun p' -> 
     let ur = None in
     get_interpretation ass (Trs.union s w) >>= fun i ->
     degree () >>= fun d ->
     return (Some (make d !(flags.dir) !(flags.dp) !(flags.tri) i p p' ur))))
;;

(* wrap into state monad *)
let (>>=) = Monad.(>>=);;
let solve fs p = 
 if Problem.is_sp p && Trs.is_srs (Problem.get_trs p) then
  Monad.get >>= fun s -> Monad.return (solve s fs p)
 else
  Monad.return None
  ;;
