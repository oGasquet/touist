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
module O = Ordinal;;



(*** TYPES ********************************************************************)

type t = {
 degree : int;
 direct : bool; 
 interpretation : (string * O.inter) list;
 reverse : bool;
 input : Problem.t;
 output :Problem.t;
};;

type flags = {
 db : int ref;
 dir : bool ref;
 help : bool ref;
 ds2 : bool ref;
 eval : bool ref;
 id : int ref;
 inter : string ref;
 min : int ref;
 neg : bool ref;
 o  : bool ref;
 ob : int ref;
 od : int ref;
 p : bool ref;
 p2 : bool ref;
 pi : bool ref;
 pr : bool ref;
 rev: bool ref;
 time : bool ref; 
 w  : bool ref; (*experimental*)
 ws : bool ref;
};;


(*** GLOBALS ******************************************************************)
let code = "eps0";;
let name = "Higher Ordinal Interpretation Processor";;
let comment = "Applies higher ordinal interpretations."
let keywords = ["ordinal interpretation";"termination"];;

let flags = {
 db = ref max_int;
 dir = ref false;
 help = ref false;
 ds2 = ref false;
 eval = ref false;
 id = ref 1;
 inter = ref "";
 min = ref 1;
 neg = ref false;
 o   = ref false;
 ob = ref max_int;
 od = ref 1;
 p = ref false;
 p2 = ref false;
 pi = ref false;
 pr = ref false;
 rev = ref false;
 time = ref false; 
 w = ref false; (*experimental*)
 ws = ref false;
};;

let spec =
 let spec = [
  ("-direct",Arg.Set flags.dir,"Try to finish termination proof.");
  ("--help",Arg.Set flags.help,"Prints information about flags.");
  ("-help",Arg.Set flags.help,"Prints information about flags.");
  ("-h",Arg.Set flags.help,"Prints information about flags.");
  ("-cache",Arg.Clear O.globals.O.cache ,"Switch off caching (default: on).");
  ("-d2",Arg.Set flags.ds2 ,"Add desired2 constraints (not monotone -> orient).");
  ("-eval",Arg.Set flags.eval,"Switch on debug output.");
  ("-ib",Arg.Int ((:=) flags.min <.> Int.bit_max),
   "Defines the number of bits used to represent matrix entries (same as \
   `-min' but in bits).");
  ("-id",Arg.Set_int flags.id,"Input degree of ordinal (default 1).");
  ("-inter",Arg.Set_string flags.inter,"Set interpretation (goodstein, \
    hydra, worms, none).");
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
  ("-od",Arg.Set_int flags.od,"Output degree of ordinal (default 1).");
  ("-p",Arg.Set flags.p,
   "Print encoding in SMT-LIB format v1.2 and fail");
  ("-p2",Arg.Set flags.p2,
   "Print encoding in SMT-LIB format v2.0 and fail");
  ("-pi",Arg.Set flags.pi,
   "Print abstract interpretation");
  ("-pr",Arg.Set flags.pr,
   "Print rules (evaluated wrt abstract interpretation)");
  ("-rev",Arg.Set flags.rev,
   "Interpret arguments in reverse order (default:off)");
  ("-t",Arg.Set flags.time,
   "Print timing information (default:off)");
  ("-ws",Arg.Set flags.ws,
   "Demand weak subterm property");
  ] in
 Arg.alignx 80 spec
;;

let help = (comment,keywords,List.map Triple.drop_snd spec);;

let rule_inter = ref []

(*** OPENS ********************************************************************)
open O;;

(*** MODULES (part 2) *********************************************************)
module Statex = struct type t = context end;;
module Made = Util.Monad.Transformer.State (Statex) (Logic.Monad);;
open Made;;

(*** FUNCTIONS ****************************************************************)
let init _ =
 flags.db := max_int;
 flags.dir := false;
 flags.help := false;
 flags.id := 1;
 flags.min := 1;
 flags.neg := false;
 flags.ob := max_int;
 flags.od := 1;
 flags.ws := false;
;;

(* Constructors and Destructors *)
let make deg dir i rev input output = {
 degree = deg;
 direct = dir;
 interpretation = i;
 reverse = rev;
 input = input;
 output = output;
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
let fprintf_var c fmt x = F.fprintf fmt "%s" (Sig.find_var_name x c);;


(* for concrete interpretations *)
let fprintf_intp_p s fmt (f,o) = 
 let rec print fmt = function
  | o when O.is_izero o -> F.fprintf fmt "0"
  | (O.O _) as o -> (
   let mono fmt i f c = 
    if Number.is_zero c then ()
    else if Number.is_one c then F.fprintf fmt "%a" (fprintf_var s) i
    else F.fprintf fmt "%a*%a" (fprintf_var s) i f c
   in
   let mono' fmt (x,c) = mono fmt x Number.fprintf c in
   let pos = List.filter (fun (x,c) -> not (Number.is_zero c)) in
   let poly sep fmt l = List.fprintf mono' sep fmt (pos l) in
   if (List.exists (fun (x,c) -> not (Number.is_zero c)) (O.inter_c o)) then
    (F.fprintf fmt "%a" (poly " + ") ((*List.rev*) (O.inter_c o));
     if not (Number.is_zero (O.inter_cexp o)) then F.fprintf fmt " + ");
   if not (Number.is_zero (O.inter_cexp o)) then (
    F.fprintf fmt "omega^(";
    print fmt (O.inter_exp o);
    F.fprintf fmt ")";
    let ce = O.inter_cexp o in
    if not (Number.is_one ce) then F.fprintf fmt "*%a" Number.fprintf ce);
   let ncs = O.inter_nc o in
   if (List.exists (fun (x,c) -> not (Number.is_zero c)) ncs) then
    F.fprintf fmt " (+) %a" (poly " (+) ") ncs;
   if not (Number.is_zero  (O.inter_c0 o)) then
    F.fprintf fmt " (+) %a" Number.fprintf (O.inter_c0 o))
 in
 let xs = O.ivars o in
 F.fprintf fmt "@[%s(%a) = %a@]" f 
  (List.fprintf (fun fmt x -> F.fprintf fmt "%a" (fprintf_var s) x) ",") xs
  print o
;;

let fprintf_intp fmt fs = Monad.get >>= fun s ->
 Monad.return (List.fprintf (fprintf_intp_p s) "@\n" fmt fs);;


let fprintf fs fmt p  = 
 F.fprintf fmt "@[<1>%s:@\ndegree: %i" name p.degree;
 F.fprintf fmt "@\nreverse arguments: %b" p.reverse;
(*HZ TODO: reverse interpretation when printing*)
 F.fprintf fmt "@\n@[<1>interpretation:@\n";
 fprintf_intp fmt p.interpretation >>= fun _ ->
 F.fprintf fmt "@]@\n@[<1>problem:@\n";
 Problem.fprintfm fmt p.output >>= fun _ ->
 F.fprintf fmt "@]@\n"; List.hd fs fmt >>= fun _ ->
 Monad.return (F.fprintf fmt "@]")
;;

(* for abstract interpretations *)
let fprintf_inter s vars fmt (f,o) = 
 let rec print fmt = function
  | O.Zero -> F.fprintf fmt "0"
  | (O.Ord _) as o ->
   let fc i fmt (x,c) = F.fprintf fmt "%a %a" (fprintf_var s) x Logic.fprintf_a c in
   let fl sep fmt = List.fprintfi fc sep fmt in
   F.fprintf fmt "%a + omega^(%!" (fl " + ") (O.cs o);
   print fmt (O.exp o);
   F.fprintf fmt ") %a (+) %a" Logic.fprintf_a (O.cexp o) (fl " (+) ") (O.ncs o);
   F.fprintf fmt " + %a%!" Logic.fprintf_a (O.c0 o)
 in
 let print_vars vars fmt xs = 
  if vars then F.fprintf fmt "(%a)" 
   (List.fprintf (fun fmt x -> F.fprintf fmt "%a" (fprintf_var s) x) ",") xs
  else F.fprintf fmt "" in
 let xs = List.map fst (O.cs o) in
 let xs = if !(flags.rev) then List.rev xs else xs in
 F.fprintf fmt "%s%a = %a" f (print_vars vars) xs print o;
;;

let print_inter s ?(vars=true)f i =
 Format.fprintf Format.std_formatter "@[%a@]@\n"
  (fun ppt -> fprintf_inter s vars ppt) (f,i)

let fprintfx fs p = failwith "XML not supported" ;;


(* Processor *)
(* administrative functions *)
let (>>=) = Made.(>>=);;

let print state f = 
 let _ = Sig.fprintf_fun Format.std_formatter f state in
 let _ = Format.printf " -> ari:%d@\n" (Sig.find_ari f state) in
 ()
;;

let context state problem =
 let arith = {
  Logic.min = Int64.of_int !(flags.min);
  neg       = false;
  rat       = 1;
  real      = false;
  minf      = false}
 in
 {arith              = arith;
  ht_avars           = Hashtbl.create 512;
  ht_con             = Hashtbl.create 512;
  ht_eq              = Hashtbl.create 512;
  ht_geq             = Hashtbl.create 512;
  ht_gt              = Hashtbl.create 512;
  ht_pvars           = Hashtbl.create 512;
  ht_zero            = Hashtbl.create 512;
  interpretations    = Hashtbl.create 512;
  gt_encodings       = Hashtbl.create 512;
  geq_encodings      = Hashtbl.create 512;
  out_deg            = !(flags.od);
  p_constraints      = Logic.top;
  p_compatible       = Logic.top;
  state              = state;
  subterm_encodings  = Hashtbl.create 512;
 }
;;

let cache_m tbl f k = 
 if Hashtbl.mem tbl k then return (Hashtbl.find tbl k)
 else (f k >>= fun v -> (Hashtbl.add tbl k v; return v))
;;

(* functions lifted from Logic into Made *)
open O.M;;
(*
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
let ($+$) = liftM2 (<+>);;
let eval_a a ass = a >>= fun a -> lift (Logic.eval_a a ass)
(* >>= fun va -> Format.printf "%a: %a@\n%!" Logic.fprintf_a a Number.fprintf va; return va *)
;;

let eval_p p ass = p >>= fun p -> lift (Logic.eval_p p ass);;
*)
let map_op op f ls = sequence (List.map f ls) >>= (return <.> op);;
let mapi_op op f ls = sequence (List.mapi f ls) >>= (return <.> op);;
let gen_op op f n = sequence (List.gen f n) >>= (return <.> op);;
let map_and f = map_op Logic.big_and f;;
let mapi_and f = mapi_op Logic.big_and f;;
let gen_and f = gen_op Logic.big_and f;;
let map_or f = map_op Logic.big_or f;;
let mapi_or f = mapi_op Logic.big_or f;;
let gen_or f = gen_op Logic.big_or f;;
let solve phi = phi >>= fun phi -> lift (Logic.solve phi);;

(* state monad interaction *)
let is_dp f = get >>= fun c -> return (Sig.is_dp f c.state);;
let arity f = get >>= fun c -> return (Sig.find_ari f c.state);;
let name f = get >>= fun c -> return (Sig.find_fun_name f c.state);;
let id f = get >>= fun c -> return (fst (Sig.to_string_fun f c.state));;
let varnames = get >>= fun c -> return (Sig.var_names c.state);;


(* encoding starts here *)
let degree () = return !(flags.id)

let rec get_vars n = 
 if n = 0 then return []
 else
  get >>= fun c -> let x,s = Sig.fresh_var c.state in
  let (_,s) = Sig.create_var_name x s in
  set {c with state=s} >>
  get_vars (n-1) >>= fun xs ->
  return (x::xs)
;;

let get_fun n = get >>= fun c ->
 let f,s = Sig.fresh_fun c.state in
 let s = Sig.add_ari f n s in
 let _,s = Sig.create_fun_name f s in
 set {c with state=s} >>= fun _ ->
 return f
;;

let set_dp f g = get >>= fun c -> 
 if Sig.is_dp f c.state then
  let g,s = Sig.set_dp g c.state in
  set {c with state=s} >>
  return g
 else 
  return g
;;

let make_interpretation f =
 arity f >>= fun a ->
 name f >>= fun n ->
 get_vars a >>= fun xs ->
 let rec make_interpretation d f = 
  if d = 0 then return O.zero
  else
   Made.sequence (List.gen (fun _ -> fresh_arith) a) >>= fun cs ->
   Made.sequence (List.gen (fun _ -> fresh_arith) a) >>= fun ncs ->
   let cs = if a = 1 then [List.hd xs,Logic.zero] else 
    List.zip_with Pair.make xs cs in
   let ncs = List.zip_with Pair.make xs ncs in
   fresh_arith >>= fun cexp ->
   fresh_arith >>= fun c0 -> 
   make_interpretation (d-1) f >>= fun exp ->
   return (O.make cs exp cexp ncs c0)
 in degree () >>= fun d -> make_interpretation d f >>= fun i ->
 name f >>= fun s ->
 get >>= fun c ->
 if !(flags.pi) then print_inter c.state s i;
 return i
;;

let make_goodstein f =
 arity f >>= fun a ->
 name f >>= fun n ->
 get_vars a >>= fun xs ->
  (* make_interpretation f >>= fun i -> *)
 let l0,l1 = Logic.zero, Logic.one in
 let o =
  if n = "C" then         
   let x::y::_ = xs in
   O.make [x,l0;y,l0] (O.make [x,l0;y,l0] O.zero l0 [x,l1;y,l0] l0) l1 [x,l0;y,l1] l1
  else if n = "h" then
   let x::y::_ = xs in
   O.make [x,l0;y,l1] (O.make [x,l0;y,l0] O.zero l0 [x,l1;y,l0] l1) l1 [x,l0;y,l0] l0
  else if n = "f" then
   let x::y::_ = xs in
   O.make [x,l0;y,l0] (O.make [x,l0;y,l0] O.zero l0 [x,l1;y,l0] l0) l1 [x,l0;y,l1] l0
  else if n = "0" then
   O.make [] (O.make [] O.zero l0 [] l0) l0 [] l0
  else
   let x::_ = xs in
   O.make [x,l0] (O.make [x,l0] O.zero l0 [x,l0] l0) l0 [x,l1] l0 
 in
 get >>= fun c ->
 if !(flags.pi) then print_inter c.state n o;
 return o
;;

let make_hydra f =
 arity f >>= fun a -> name f >>= fun n ->  
 get_vars a >>= fun xs ->
 let l0,l1 = Logic.zero, Logic.one in
 let o =
  if n = "H" then
   let x::y::_ = xs in
   O.make [x,l0;y,l0] (O.make [x,l0;y,l0] O.zero l0 [x,l1;y,l0] l0) l1 [x,l0;y,l1] l0
  else if n = "c" || n = "c1" then
   let x::y::_ = xs in
   O.make [x,l0;y,l1] (O.make [x,l0;y,l0] O.zero l0 [x,l1;y,l0] l1) l1 [x,l0;y,l0] l0
  else if n = "C" || n = "c2" then
   let x::y::z::_ = xs in
   let fxy = O.make [x,l0;y,l1;z,l0] 
    (O.make [x,l0;y,l0;z,l0] O.zero l0 [x,l1;y,l0;z,l0] l1) l1 [x,l0;y,l0;z,l0] l0 in
    O.make [x,l0;y,l0;z,l0] fxy l1 [x,l0;y,l0;z,l1] l0
  else if n = "0" then
   O.make [] (O.make [] O.zero l0 [] l0) l0 [] l1
  else
   let x::_ = xs in
   O.make [x,l0] (O.make [x,l0] O.zero l0 [x,l0] l0) l0 [x,l1] l0
 in
 get >>= fun c ->
 if !(flags.pi) then print_inter c.state n o;
 return o
;;

(*
let make_worms f =
 arity f >>= fun a ->
 name f >>= fun n ->
 get_vars a >>= fun xs ->
 (* make_interpretation f >>= fun i -> *)
 let l0,l1 = Logic.zero, Logic.one in
 let o =
  if n = "m" || n = "." then
   let x::y::_ = xs in
   O.make [x,l1;y,l1] (O.make [x,l0;y,l0] O.zero l0 [x,l0;y,l0] l0) l0 [x,l0;y,l0] l0
  else if (n = "c") || (n = "f") then
   let x::_ = xs in
   O.make [x,l0] (O.make [x,l0] O.zero l0 [x,l1] l0) l1 [x,l0] l0
  else if n = "0" then
   O.make [] (O.make [] O.zero l0 [] l0) l0 [] l1
  else
   let x::_ = xs in
   O.make [x,l0] (O.make [x,l0] O.zero l0 [x,l0] l0) l0 [x,l1] l0
 in
 get >>= fun c ->
 if !(flags.pi) then print_inter c.state n o;
 return o
;;
*)

let add_constraint p = 
 get >>= fun c ->
 set {c with p_constraints = c.p_constraints <&> p}
;;

let make_worms f =
 arity f >>= fun a ->
 name f >>= fun n ->
 get_vars a >>= fun xs ->
 let l0,l1 = Logic.zero, Logic.one in
 (
  if n = "app" || n = "." then
   let x::y::_ = xs in
   return (O.make [x,l1;y,l1] O.zero l0 [x,l0;y,l0] l0)
   else if n = "f" then
   let x::_ = xs in
   return (O.make [x,l0] (O.make [x,l1] O.zero l0 [x,l0] l0) l1 [x,l0] l0)
  else if n = "c" || n = "c#" then
   let x::_ = xs in
   return (O.make [x,l0] O.zero l0 [x,l1] l1)
  else if n = "0" then
   return (O.make [] O.zero l0 [] l1)
  else if n = "b" || n = "a" || n = "b1" then
   let x::_ = xs in
   return (O.make [x,l0] O.zero l0 [x,l1] l0)
   else 
   make_interpretation f
 ) >>= fun o ->
 get >>= fun c ->
 if !(flags.pi) then print_inter c.state n o;
 return o
;;

let make_worm2 f =
 arity f >>= fun a ->
 name f >>= fun n ->
 get_vars a >>= fun xs ->
 let l0,l1 = Logic.zero, Logic.one in
 fresh_arith >>= fun a0 ->
 fresh_arith >>= fun a1 ->
 fresh_arith >>= fun a2 ->
 fresh_arith >>= fun a3 ->
 fresh_arith >>= fun a4 ->
 add_constraint (a0 <=> l0)>>
 add_constraint (a1 <=> l1)>>
 (
  if n = "app" || n = "." then
   let x::y::_ = xs in
   return (O.make [x,l1;y,l1] O.zero l0 [x,l0;y,l0] l1)
   else if n = "f" then
   let x::_ = xs in
   return (O.make [x,l0] (O.make [x,l1] O.zero l0 [x,l0] l0) l1 [x,l0] l0)
  else if n = "c" || n = "c#" then
   let x::_ = xs in
   return (O.make [x,l0] O.zero l0 [x,l1] l1)
  else if n = "0" then
   return (O.make [] O.zero l0 [] l1)
  else if n = "b" || n = "a" || n = "b1" then
   let x::_ = xs in
   return (O.make [x,l0] O.zero l0 [x,l1] l0)
   else 
   make_interpretation f
 ) >>= fun o ->
 get >>= fun c ->
 if !(flags.pi) then print_inter c.state n o;
 return o
;;

let make_fab f =
 arity f >>= fun a ->
 name f >>= fun n ->
 get_vars a >>= fun xs ->
  (* make_interpretation f >>= fun i -> *)
 let l0,l1 = Logic.zero, Logic.one in
 Made.sequence (List.gen (fun _ -> fresh_arith) 6) >>= fun [c0;c1;c2;c3;c4;c5] ->
 let o =
  if n = "f" then         
   let x::y::_ = xs in
   O.make [x,l1;y,l1] (O.zero) c2 [x,l0;y,l0] l0
  else 
   O.make [] (O.zero) l0 [] l1
 in
 get >>= fun c ->
 if !(flags.pi) then print_inter c.state n o;
 return o
;;

let make_toyama f = 
 arity f >>= fun a ->
 get_vars 3 >>= fun [x;y;z] ->
 let l0,l1 = Logic.zero, Logic.one in
 name f >>= fun n ->
 (match n with
 | "f" -> return (O.make [x,l1;y,l0;z,l0] 
           (O.make [x,l0;y,l0;z,l1] O.zero l0 [x,l0;y,l0;z,l0] l1) l1 [x,l0;y,l1;z,l0] l0)
 | "0" -> return (O.make [] O.zero l0 [] l0)
 | "1" -> return (O.make [] O.zero l0 [] l1)
 | "g" -> return (O.make [x,l0;y,l0] O.zero l0 [x,l1;y,l1] l1)
 | _ -> make_interpretation f
 ) >>= fun o ->
 get >>= fun c ->
 if !(flags.pi) then print_inter c.state n o;
 return o
;;

let make_bug f = 
 arity f >>= fun a ->
 get_vars 3 >>= fun [x;y;z] ->
 let l0,l1 = Logic.zero, Logic.one in
 name f >>= fun n ->
 (match n with
 | "h" -> return (O.make [x,l1;y,l0] O.zero l0 [x,l0;y,l1] l0)
 | "f" -> return (O.make [x,l1;y,l0] (O.make [x,l0;y,l1] O.zero l0 [x,l0;y,l0] l1) l1 [x,l0;y,l1] l0)
 | _ -> make_interpretation f
 ) >>= fun o ->
 get >>= fun c ->
 if !(flags.pi) then print_inter c.state n o;
 return o
;;


let interpretation f = 
 get >>= fun c ->
 let make_i = if !(flags.inter) = "goodstein" then make_goodstein
  else if !(flags.inter) = "hydra" then make_hydra
  else if !(flags.inter) = "worms" then make_worms
  else if !(flags.inter) = "worm2" then make_worm2
  else if !(flags.inter) = "fab" then make_fab
  else if !(flags.inter) = "toyama" then make_toyama
  else if !(flags.inter) = "bug" then make_bug
  else make_interpretation
 in
 cache_m c.interpretations make_i f
;;

(*not side-effect free*)
let eval txt p = 
 if not !(flags.eval) then (return p)
 else
  (return p) $&$ O.side_conditions () >>= fun phi ->
  (* solve (return phi) >>= fun a -> *)
  let a = Logic.run ~obits:!(flags.ob) (Logic.solve phi) in
  let b = match a with 
   | None -> false
   | Some _ -> true
  in Format.printf "%s: %b@\n@?" txt b;
  return p
;;

let rec encode_term t = get >>= fun c ->
 cache_m c.subterm_encodings etc t
and etc = function
 | Term.Var x -> 
  (* fresh_bool >>= fun b1 -> fresh_bool >>= fun b2 -> return (O.make_bool_var b1 x,O.make_bool_var b2 x) *)
 (* return (O.make_ord_var x,O.make_var x) *)
 return (O.make_var x, O.make_var x)
 | (Term.Fun (f,[])) -> interpretation f >>= fun o -> return (o,o)
 | (Term.Fun (f,ts)) ->
  let ts = if !(flags.rev) then List.rev ts else ts in
  interpretation f >>= fun o ->
  (*HZ: sound if all terms different*)
  if List.for_all Term.is_var ts && (List.unique ts = ts) then
   let to_var = function Term.Var x -> x | _ -> failwith "no var" in
   let o' = O.substitute_vars (List.map to_var ts) o in
   return (o',o')
  else
   map encode_term ts >>= fun os ->
   interpretation f >>= O.interpret_with_args os
;;



let greater_equal_rule rule = 
 encode_term (Rule.lhs rule) >>= fun (_,ll) ->
 encode_term (Rule.rhs rule) >>= fun (ur,_) ->
 (if !(flags.pr) then (
  get >>= fun c -> let s = c.state in
  let (s,l) = Term.to_strings s (Rule.lhs rule) in
  let (s,r) = Term.to_strings s (Rule.rhs rule) in
  print_inter s ~vars:false l ll;
  print_inter s ~vars:false r ur;
  return ())
 else return ()) >>= fun _ ->
 rule_inter := (ll,ur) :: !rule_inter;
 O.geq ll ur 
 (* >>= fun enc -> let _ = Format.eprintf "@\nenc: %a@\n@?" Logic.fprintf_p enc in return enc *)
 >>= eval " geq"
;;

let greater_equal_rule rule = get >>= fun c ->
 if Rule.is_embedded rule then
  return Logic.top 
 else
  cache_m c.geq_encodings (greater_equal_rule) rule
;;

let greater_rule rule = 
 if Rule.is_embedded rule && not !(flags.ws) then 
  return Logic.top 
 else if Term.is_var (Rule.rhs rule) then
  encode_term (Rule.lhs rule) >>= fun (_,ll) ->
  let x = match (Rule.rhs rule) with | Term.Var x -> x in
  O.con x ll $&$ return (((O.c0 ll <>> Logic.zero) <|> (O.cexp ll <>> Logic.zero)))
 else 
  encode_term (Rule.lhs rule) >>= fun (_,ll) ->
  encode_term (Rule.rhs rule) >>= fun (ur,_) ->
  get >>= fun c ->
 (if !(flags.pr) then (
  get >>= fun c -> let s = c.state in
  let (s,l) = Term.to_strings s (Rule.lhs rule) in
  print_inter s ~vars:false l ll;
  let (s,r) = Term.to_strings s (Rule.rhs rule) in
  print_inter s ~vars:false r ur;
  return ())
 else return ()) >>= fun _ ->
  O.gt ll ur 
  >>= eval "gt" 
;;

let greater_rule rule = get >>= fun c ->
 cache_m c.gt_encodings greater_rule rule
;;

let encode_geq s w = map_and greater_equal_rule (s@w);;

let encode_gt s w = get >>= fun c -> 
 let s = if !(flags.dir) then s else List.rev_append s w in
 let op = (if !(flags.dir) then Logic.big_and else Logic.big_or) in
 map_op op greater_rule s
;;

(* demand (weakly) simple interpretations *)

(* actually, we restrict such that every variable occurs either with
   standard or natural addition or in the exponent *)
let weakly_simple_f f =
 arity f >>= fun a ->
 if a = 0 then return Logic.top else
  interpretation f >>= fun o ->
(*HZ TODO: not all variables contained in cs part*)
  map (fun x -> O.con x o) (List.map fst (O.cs o)) >>= fun xs_cons ->
  name f >>= fun f ->
  return (Logic.big_and xs_cons)
   (* >>= eval f *)
;;

let simple_f f = 
 interpretation f >>= fun o ->
 weakly_simple_f f >>= fun ws ->
 return (((O.c0 o <>> Logic.zero) <|> (O.cexp o  <>> Logic.zero)) <&> ws)
;;

let weakly_simple fs = map_and weakly_simple_f fs;;

let simple fs = map_and simple_f fs;;

(* some desired properties (restrictions!) *)
let desired_f f =
 arity f >>= fun a ->
 let max1 a b c = (a <->> ~!(b <|> c)) <&> (b <->> ~!(a <|> c)) <&>
  (c <->> ~!(a <|> b)) in
 let rec des = function
  | O.Zero -> return Logic.top
  | (O.Ord _) as o ->
   (* we want just one constant part *)
   O.is_zero (O.exp o) >>= fun exp_zero ->
   let const = (exp_zero <->> (O.cexp o <=> Logic.zero)) in
   (* no variable x is considered in both natural and standard addition *)
   let xs = List.map fst (O.cs o) in
   let p a = a <>> Logic.zero in
   let b x = 
    O.con x (O.exp o) >>= fun con ->
    return (max1 (p (O.c (O.cs o) x)) (p (O.c (O.ncs o) x)) con) 
   in
   map b xs >>= fun max1xs ->
   (* exponent only if variable considered *)
   map (fun x -> O.con x (O.exp o)) xs >>= fun con_xs ->
   let exp_con = (O.cexp o <>> Logic.zero) <->> (Logic.big_or con_xs) in
   (* exponent should have desired form as well *)
   des (O.exp o) >>= fun exp_ok ->
   return (Logic.big_and max1xs <&> const <&> exp_ok <&> exp_con)
 in interpretation f >>= des
;;

let desired fs = map_and desired_f fs;;

(*HZ NOTE: see analogue mon_f criterion*)
let rec mon_f = function
 | O.Zero -> Logic.bot
 | o -> let geq_one x = x <>=> Logic.one in
  let xs = O.vars o in
  Logic.big_and (List.map (fun x -> geq_one (O.c (O.ncs o) x)) xs)
  <|> (geq_one (O.cexp o) <&> mon_f (O.exp o)) 
;;

let aux2 rule = 
 let (l,r) = Rule.to_terms rule in
 if Term.is_var r then (
  let x = match r with Term.Var r -> r in
  let fs = Term.funs l in
  Made.sequence (List.map interpretation fs) >>= fun fs ->
  let mon = Logic.big_and (List.map mon_f fs) in
  return (~! mon) 
 ) else return Logic.bot
;;

let desired2_rule rule = 
 let (l,r) = Rule.to_terms rule in
 let f = Option.the (Term.root l) in
 interpretation f >>= fun o ->
 let monf = mon_f o in
 aux2 rule >>= fun aux2 ->
 return ((~! monf) <|> aux2) $->$ greater_rule rule
 
let desired2 trs = map_and desired2_rule (Trs.to_list trs)

(* weak monotonicity is for free *)
let wmon_f f = return Logic.top

let wmon fs = map_and wmon_f fs;;

let encode strict weak = get >>= fun c ->
 let (s, w) = Pair.map Trs.to_list (strict, weak) in
 let fs = Trs.funs (Trs.union strict weak) in
 encode_geq s w $&$
 encode_gt s w $&$
 ((if !(flags.ws) then weakly_simple else simple) fs) $&$
 (desired fs) $&$
 (if !(flags.ds2) then desired2 (Trs.union strict weak) else return Logic.top) $&$
 (O.side_conditions ()) $&$
 return Logic.top
;;

(* decoding *)
let rec eval_interpretation ass = function
   O.Zero -> return O.Z
 | (O.Ord o) as t ->
  let seq = map (fun (x,a) -> eval_a (return a) ass >>= fun n -> 
 (*Format.printf "%a has value %a\n%!" Logic.fprintf_a a Number.fprintf n;*)
 return (x,n)) in
  seq (O.cs t) >>= fun cs ->
  seq (O.ncs t) >>= fun ncs ->
  eval_a (return (O.cexp t)) ass >>= fun cexp ->
  eval_a (return (O.c0 t)) ass >>= fun c0 ->
  eval_interpretation ass (O.exp t) >>= fun exp ->
  return (O.make_inter cs exp cexp ncs c0)
;; 

let get_interpretation ass f = name f >>= fun name ->
 interpretation f >>= fun i ->
 eval_interpretation ass i >>= fun evi ->
 return (name,evi)
;;

let make_interpretation ass trs =
 (*print_interpreted_rules ass >> *)
 Made.sequence (List.map (get_interpretation ass) (Trs.funs trs))
;;

let decode_rule ass rule = liftM not (eval_p (greater_rule rule) ass);;

let decode_trs ass trs = 
 Made.filter (decode_rule ass) (Trs.to_list trs) >>= (return <.> Trs.of_list)
;;

let decode_weak ass w = decode_trs ass w;;

(* prerequisite: all variables are present *)
(*HZ TODO: improve criterion, i.e., x1 + y0 + omega^0 0 + x0 (+) y1 is not detected monotone*)
(*HZ NOTE: see analogue mon_f criterion*)
let rec mon_fx x = function
 | O.Z -> false
 | o -> let geq_one x = Number.ge x Number.one in
  let last = try match List.last (O.inter_c o) with
    (y,c) when x = y -> c
   with _ -> Number.zero in
  (O.inter_cexp o = Number.zero && geq_one last) ||
  (geq_one (O.ci (O.inter_nc o) x)) ||
  (geq_one (O.inter_cexp o) && mon_fx x (O.inter_exp o))

let rec mon_f = function
 | O.Z -> false
 | o -> List.for_all (fun x -> mon_fx x o) (O.ivars o)
;;

let add_mon_rule f inter = 
 if mon_f inter then return []
 else
  arity f >>= fun a ->
  let xs = (O.ivars inter) in
  let xs = if !(flags.rev) then List.rev xs else xs in
  let ys = List.filter (fun x -> mon_fx x inter) xs in
  get_fun (List.length ys) >>= fun f_fresh ->
  set_dp f f_fresh >>= fun f_fresh ->
  let l = Term.make_fun f_fresh (List.map Term.make_var ys) in
  let r = Term.make_fun f (List.map Term.make_var xs) in
  return ([Rule.of_terms l r]) 
;;

let decode_mon ass fs =
 (* if !(flags.ds2) then *)
 Made.sequence (List.map (fun f -> 
  get_interpretation ass f >>= fun (n,intp) ->
  add_mon_rule f intp) fs) >>= fun rs ->
 return (Trs.of_list (List.concat rs))
 (* else return Trs.empty *)
;;

let decode ass p = get >>= fun c -> 
 let (s,w) = Problem.get_sw p in
 decode_trs ass s >>= fun s' ->
 decode_weak ass w >>= fun w' ->
 decode_mon ass (Trs.funs (Trs.union s w)) >>= fun w'' ->
 return (Problem.set_sw s' (Trs.union w' w'') p)
;;


let print_interpreted_rules ass =
 let p (l,r) =
  eval_interpretation ass l >>= fun ll ->
  eval_interpretation ass r >>= fun rr ->
  get >>= fun c -> 
  Format.fprintf Format.std_formatter "@[%a@]@\n" (fprintf_intp_p c.state) ("l",ll);
  Format.fprintf Format.std_formatter "@[%a@]@\n" (fprintf_intp_p c.state) ("r",rr);
(*  let l',r' = (O.exp l),(O.exp r) in
  let b = O.gt l' r' in
  eval_p b ass >>= fun b ->
  Format.fprintf Format.std_formatter "@[exp gt? %i@]@\n" (if b then 1 else 0);
  let l',r' = (O.exp l'),(O.exp r') in
  let b = O.gt l' r' in
  eval_p b ass >>= fun b ->
  Format.fprintf Format.std_formatter "@[exp gt? %i@]@\n" (if b then 1 else 0);*)
  return () 
 in
 iter p !rule_inter
;;

let print_formula fs phi = get >>= fun c -> 
 let fprintf_formula = 
  if !(flags.p) then Logic.fprintf_smt 
  else if !(flags.p2) then Logic.fprintf_smt2
  else failwith (code ^ ".flag p or p2 expected")
  in
 let logic = "QF_NIA" in
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
   let t = Unix.gettimeofday () in
   Made.lift (Logic.solve phi) >>= function
    | None -> return None
    | Some ass -> 
    if !(flags.time) then (
     let t = Unix.gettimeofday () -. t in
     Format.printf "time in solver: %f\n%!" t;
     Format.printf "time in compose: %f\n%!" !O.t_compose;
     Format.printf "time in compare: %f\n%!" !O.t_compare;
     Format.printf "time in add: %f\n%!" !O.t_add;
     Format.printf "time in nadd: %f\n%!" !O.t_nadd;
    );
     decode ass p >>= fun p' -> 
     make_interpretation ass (Trs.union s w) >>= fun i ->
     degree () >>= fun d ->
     get >>= fun c -> 
     return (Some (c.state,make d !(flags.dir) i !(flags.rev) p p'))))
;;

(* wrap into state monad *)
let (>>=) = Monad.(>>=);;
let (>>) = Monad.(>>);;
let solve fs p =
 if (Problem.is_sp p) || (Problem.is_rp p) || (Problem.is_dp p)  then
  Monad.get >>= fun s -> match solve s fs p with
    | None -> Monad.return None
    | Some (s,p) -> Monad.set s >> Monad.return (Some p)
 else
  Monad.return None
;;
