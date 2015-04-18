(* Copyright 2012 Sarah Winkler, Harald Zankl
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
module N = Logic.Number;;
module L = Logic;;
module V = Variable;;
module F = Format;;
module Monad = Rewritingx.Monad;;
module Fun = Function;;
module Sig = Signature;;

(*** TYPES ********************************************************************)
type o = { cs:   (V.t * L.a) list;
           exp:  t;
           cexp: L.a;
           ncs:  (V.t * L.a) list;
           c0:   L.a 
         }
and  t = Zero | Ord of o

type inter_o = { 
           ics:   (V.t * L.Number.t) list;
           iexp:  inter;
           icexp: L.Number.t;
           incs:  (V.t * L.Number.t) list;
           ic0:   L.Number.t
         }
and inter = Z | O of inter_o

type context = {
 arith              : Logic.arith;
 interpretations    : (Fun.t, t) Hashtbl.t;
 ht_con             : (V.t * t, Logic.p * Logic.p) Hashtbl.t;
 ht_geq             : (t * t, Logic.p * Logic.p) Hashtbl.t;
 ht_gt              : (t * t, Logic.p * Logic.p) Hashtbl.t;
 ht_eq              : (t * t, Logic.p * Logic.p) Hashtbl.t;
 ht_avars           : (Logic.a, Logic.a) Hashtbl.t;
 ht_pvars           : (Logic.p, Logic.p) Hashtbl.t;
 ht_zero            : (t, Logic.p * Logic.p) Hashtbl.t;
 gt_encodings       : (Rule.t,Logic.p) Hashtbl.t;
 geq_encodings      : (Rule.t,Logic.p) Hashtbl.t;
 out_deg            : int;
 p_constraints      : Logic.p;
 p_compatible       : Logic.p;
 state              : Sig.t;
 subterm_encodings  : (Term.t,t * t) Hashtbl.t;
};;

type globals = {
 cache : bool ref;
}

(*** MODULES (part 2) *********************************************************)
module Statex = struct type t = context end;;
module Made = Util.Monad.Transformer.State (Statex) (Logic.Monad);;
open Made;;

(*** GLOBALS ******************************************************************)
let globals = {
 cache = ref true;
};;

let t_compose = ref 0.0;;
let t_compare = ref 0.0;;
let t_add = ref 0.0;;
let t_nadd = ref 0.0;;

(*** FUNCTIONS ****************************************************************)

let (>>=) = Monad.(>>=);;

(* printers *)
let fprintf_inter fmt (f,o) =
 let detail = true in
 let fprintf_coeff fmt c = if detail then Logic.fprintf_a fmt c 
                                    else Format.fprintf fmt "_" in
 let rec print fmt = function
  | Zero -> F.fprintf fmt "0"
  | Ord o ->
   let fc _ fmt (x,c) = F.fprintf fmt "v%i %a" (V.to_int x) fprintf_coeff c in
   let fl sep fmt = List.fprintfi fc sep fmt in
   F.fprintf fmt "%a + omega^(%!" (fl " + ") o.cs;
   print fmt o.exp;
   F.fprintf fmt ") %a (+) %a" fprintf_coeff o.cexp (fl " (+) ") o.ncs;
   F.fprintf fmt " + %a%!" fprintf_coeff o.c0;
 in F.fprintf fmt "%s(x) = %a" f print o
;;

let print_inter f i =
 Format.fprintf Format.std_formatter "@[%a@]@\n"
  (fun ppt -> fprintf_inter ppt) (f,i)

let print_all =
 List.iter (print_inter "-")

(* administrative functions *)
let (>>=) = Made.(>>=);;

(* functions lifted from Logic into Made *)
module M = struct
let fresh_arith = get >>= fun s -> lift (Logic.fresh_arith s.arith);;
let fresh_arith_spec arith = lift (Logic.fresh_arith arith);;
let fresh_bool = get >>= fun s -> lift Logic.fresh_bool;;
let nm = liftM (~!);;
let ($&$) = liftM2 (<&>);;
let ($|$) = liftM2 (<|>);;
let ($->$) = liftM2 (<->>);;
let ($<->$) = liftM2 (<<->>);;
let ($<$) = liftM2 (<<>);;
let ($>$) = liftM2 (<>>);;
let ($>=$) = liftM2 (<>=>);;
let ($<=$) = liftM2 (<<=>);;
let ($+$) = liftM2 (<+>);;
let iteM = liftM3 L.ite
let eval_a a ass = a >>= fun a -> lift (Logic.eval_a a ass);;
let eval_p p ass = p >>= fun p -> lift (Logic.eval_p p ass);;
end
open M;;

(* state monad interaction *)
let arity f = get >>= fun c -> return (Sig.find_ari f c.state);;

(* to store formulas and associate them with a fresh variable *)
let cache_m tbl f k =
 if not !(globals.cache) then f k else
 if Hashtbl.mem tbl k then return (fst (Hashtbl.find tbl k))
 else
  f k >>= fun v -> 
  if (v = L.top) || (v = L.bot) then
   (Hashtbl.add tbl k (v,v); return v)
  else
   (fresh_bool >>= fun b ->
   Hashtbl.add tbl k (b,v); return b)
;;

(* here ordinal interpretations start *)
(* constructors and destructors *)
let cs = function Ord o -> o.cs | _ -> failwith "c: is Zero";;
let exp = function Ord o -> o.exp | _ -> failwith "exp: is Zero";;
let cexp = function Ord o -> o.cexp | _ -> failwith "cexp: is Zero";;
let ncs = function Ord o -> o.ncs | _ -> failwith "nc: is Zero";;
let c0 = function Ord o -> o.c0 | _ -> failwith "c0: is Zero";;
let c cs x = try List.assoc x cs with Not_found -> L.zero;;
let zero = Zero;;
let make_o c e ce nc c0 = {cs=c; exp=e; cexp=ce; ncs=nc; c0=c0};;
let make c e ce nc c0 = Ord (make_o c e ce nc c0);;
let inter_c = function O o -> o.ics | _ -> failwith "c: is Zero";;
let inter_exp = function O o -> o.iexp | _ -> failwith "exp: is Zero";;
let inter_cexp = function O o -> o.icexp | _ -> failwith "cexp: is Zero";;
let inter_nc = function O o -> o.incs | _ -> failwith "nc: is Zero";;
let inter_c0 = function O o -> o.ic0 | _ -> failwith "c0: is Zero";;
let ci cs x = try List.assoc x cs with Not_found -> L.Number.zero;;

let make_inter cs exp cexp ncs c0 = 
 O {ics=cs; iexp=exp; icexp=cexp; incs=ncs; ic0=c0}
;;

let rec depth = function Zero -> 0 | Ord f -> 1 + (depth f.exp) 

(*check for compatible variable order*)
let rec compatible_var = function
 | [],_ | _,[] -> true
 | x::xs,y::ys when x = y -> compatible_var (xs,ys)
 | x::xs,ys when not (List.mem x ys) -> compatible_var (xs,ys)
 | xs,y::ys when not (List.mem y xs) -> compatible_var (xs,ys)
 | _ -> false
;;

let relevant_vars cs = 
 (*monomials with zero coefficients can be ignored *)
 let cs = List.filter (fun (x,c) -> c <> Logic.zero) cs in
 List.map fst cs
;;

let rec compatible = function
 | Zero,_ | _,Zero -> true
 | Ord ff, Ord gg ->
 let xs,ys = Pair.map relevant_vars (ff.cs,gg.cs) in
 compatible_var (xs,ys) && compatible (ff.exp,gg.exp)
;;

let compatible f g = get >>= fun c ->
 if compatible (f,g) then 
 return () else (
 (* Format.eprintf "variable order not compatible@\n%!"; *)
 get >>= fun c ->
 set {c with p_compatible = Logic.bot};
 return ())
;;

(* auxiliary to add coefficient lists *)
let combine f x y = 
 let rec combine = function
   [], cs -> cs
 | cs, [] -> cs
 | (x,a)::cs,cs' when not (List.mem_assoc x cs') -> (x,a)::(combine (cs,cs'))
 | (x,a)::cs,cs' -> 
  let b = List.assoc x cs' in (x,f a b)::(combine (cs,List.remove (x,b) cs'))
 in combine (x,y)
;;

let add_nat_coeff x a = function
 | Zero -> failwith "add std coeff: Zero"
 | Ord o ->
 let ncs = if List.mem_assoc x o.ncs then
  (x,List.assoc x o.ncs <+> a)::(List.remove_assoc x o.ncs)
 else (x,a)::o.ncs in
 Ord {o with ncs=ncs}
;;

let add_nat_coeffs cs (Ord f) = Ord {f with ncs = combine (<+>) f.ncs cs};;
let add_std_coeffs cs (Ord f) = Ord {f with cs = combine (<+>) f.cs cs};;

let add_std_coeff x a = function
 | Zero -> failwith "add std coeff: Zero"
 | Ord o ->
 let cs = if List.mem_assoc x o.cs then
  (x,List.assoc x o.cs <+> a)::(List.remove_assoc x o.cs)
 else (x,a)::o.cs in
 Ord {o with cs=cs}
;;

let is_mono f =
 (f.cexp = L.zero) && (f.cs = []) && (f.c0 = L.zero) && 
 (List.length f.ncs = 1)
;;

let is_empty = List.for_all (fun (_,a) -> a = L.zero);;
let only_std f = (f.cexp = L.zero) && (is_empty f.ncs) && (f.c0 = L.zero);;
let only_nat f = (f.cexp = L.zero) && (is_empty f.cs) && (f.c0 = L.zero);;
let mono f = List.hd f.ncs;;
let make_mono_std = function 
 Ord f -> Ord {f with cs = f.ncs; ncs=[]} | Zero -> Zero
;;

(* upper bound for two ordinals *)
let rec omax f g =
 let max = Logic.max in (* SW *)
 let mmax fs gs = combine max fs gs in
 let omax = function
  | Zero, g -> g
  | f, Zero -> f
  | f,g -> 
   make (mmax (cs f) (cs g)) (omax (exp f) (exp g)) (max (cexp f) (cexp g)) 
    (mmax (ncs f) (ncs g)) (max (c0 f) (c0 g))
 in omax (f,g)
;;

(* lower bound for two ordinals *)
let rec omin f g =
 let min = Logic.min in (* SW *)
 let mmin fs gs = combine min fs gs in
 let omin = function
  | Zero, _
  | _, Zero -> Zero
  | f,g -> 
   make (mmin (cs f) (cs g)) (omin (exp f) (exp g)) (min (cexp f) (cexp g)) 
    (mmin (ncs f) (ncs g)) (min (c0 f) (c0 g))
 in omin (f,g)
;;

(* formulas for simple properties *)
let is_pos e = 
 if e = L.zero then L.bot 
 else if e = L.one then L.top
 else (e <>> L.zero)

let all_zero = L.big_and <.> List.map ( fun (_,c) -> c <=> L.zero)

let is_zero f =
 get >>= fun c ->
 let is_zero' = function
  | Zero -> return L.top
  | Ord f -> 
   let z x = L.zero <=> x in
   let zs = L.big_and <.> List.map (z <.> snd) in
   return (L.big_and [zs f.cs; z f.cexp; zs f.ncs; z f.c0])
 in 
 (* cache_m c.ht_zero  *)
is_zero' f
;;

let is_izero = function
  | Z -> true
  | O f ->
   let z x = N.zero = x in
   let zs = List.for_all (z <.> snd) in
   (zs f.ics) && (z f.icexp) && (zs f.incs) && (z f.ic0)
;;

let rec is_gt_zero = function
 | Zero -> L.bot
 | Ord f ->
  (*no recursive descent necessary*)
  (is_pos f.c0) <|> ((is_pos f.cexp) (* <&> (is_gt_zero f.exp)*))
;;

let is_constant f = 
 let z x = L.zero <=> x in
 let zs = L.big_and <.> List.map (z <.> snd) in
 is_zero f.exp >>= fun zero_f' ->
 return (L.big_and [zs f.cs; zero_f' <|> (z f.cexp); zs f.ncs])
;;

let is_var = function
 | Zero -> L.bot
 | Ord f ->
  let sum = L.big_sum (List.map snd f.ncs) in
  L.big_and [all_zero f.cs; f.cexp <=> L.zero; sum <=> L.one; f.c0 <=> L.zero]
;;

(* expression stating whether argument i is considered *)
let con x f =
 get >>= fun cxt ->
 let rec con = function
  | x, Zero -> return L.bot
  | x, Ord f -> 
   is_zero (Ord f) >>= fun f_is_zero ->
   con (x,f.exp) >>= fun con_exp ->
   return ((~! f_is_zero) <&> ((con_exp <&> (is_pos f.cexp)) <|> 
    (is_pos (c f.cs x)) <|> (is_pos (c f.ncs x))))
 in 
(* cache_m cxt.ht_con  *)
con (x,f)

let conw x f = (con x f.exp) $&$ (return (is_pos f.cexp))

let rec vars = function
  | Zero -> []
  | Ord f ->
   List.unique ((List.map fst f.cs) @ (List.map fst f.ncs) @ (vars f.exp))
;;

let rec ivars = function
  | Z -> []
  | O f ->
   List.unique ((List.map fst f.ics) @ (List.map fst f.incs) @ (ivars f.iexp))
;;

(* scalar multiplication *)
let mult a = function
 | Zero -> (Zero,Zero)
 | Ord f ->
  if a = L.zero then (Zero,Zero)
  else
   let mulu = List.map (fun (x,b) -> (x,b<*>a)) in
   let u = make (mulu f.cs) f.exp (f.cexp <*> a) (mulu f.ncs) (f.c0 <*> a) in
   let la = L.ite (a <=> L.zero) L.zero a in
   let mull = List.map (fun (x,b) -> (x,b<*>la)) in
   let l1 = L.ite (a <=> L.zero) L.zero L.one in
   let mul1 = List.map (fun (x,b) -> (x,b<*>l1)) in
   let l = make (mul1 f.cs) f.exp (f.cexp <*> la) (mull f.ncs) (f.c0 <*> a) in
   (u,l)
;;

(* adding a constant from the right *)
let const_add c0 = function
 | Zero -> make [] Zero L.zero [] c0
 | Ord f -> make f.cs f.exp f.cexp f.ncs (f.c0 <+> c0)
;;

(* f >= g *)
let rec geq f g =
 (* print_inter "l" f; *)
 (* print_inter "r" g; *)
 get >>= fun c ->
 let geq' = function
   | _, Zero -> return L.top
   | Zero, gg -> is_zero gg
   | (Ord f) as ff, ((Ord g) as gg) -> 
    let all = (liftM L.big_and) <.> (map (geqx ff gg)) in
     ((all (vars gg) 
 (* >>= (fun enc -> Format.printf "@\ngeq:%a@\n@?" L.fprintf_p enc; return enc) *)
)
$&$ geq0 ff gg) 
 in
 compatible f g >>= fun _ ->  
 cache_m c.ht_geq geq' (f,g)

and geq0 ff gg =
 match ff,gg with
  | _, Zero -> return L.top
  | Zero, _ -> is_zero gg
  | Ord f, Ord g ->
   gt0 f.exp g.exp >>= fun gt0_exp ->
   geq0 f.exp g.exp >>= fun geq0_exp ->
   let phi = 
    (gt0_exp <&> (is_pos f.cexp)) <|> 
    ((geq0_exp <&> (f.cexp <>=> g.cexp)) <&> (f.c0 <>=> g.c0)) <|> 
    ((g.cexp <=> L.zero) <&> (f.c0 <>=> g.c0))
   in return phi

and geqx ff gg x =
 match ff,gg with
  | _, Zero -> return L.top
  | Zero, _ -> is_zero gg
  | Ord f, Ord g ->
   con x (Ord g) >>= fun con_g ->
   conw x f >>= fun con_x_fe ->
   conw x g >>= fun con_x_ge ->
   geqx f.exp g.exp x >>= fun geqx_exp ->
   is_zero g.exp >>= fun zero_g' ->
   is_zero f.exp >>= fun zero_f' ->
   let phi =
    (~! con_g) 
    <|> (geqx_exp <&> (f.cexp <>=> g.cexp) <&>
     (c g.cs x <=> L.zero) <&> (c g.ncs x <=> L.zero))
    <|> (con_x_fe <&> ~! con_x_ge)
    <|> (con_x_fe <&> geqx_exp <&> (f.cexp <>> g.cexp))
    <|> (con_x_fe <&> geqx_exp <&> (f.cexp <=> g.cexp) <&>
        ((c f.ncs x) <>=> (c g.ncs x)))
    <|> ((~! con_x_ge) <&> 
     ((c f.ncs x) <>=> (c g.ncs x)) <&>
     ((c f.ncs x <+> (c f.cs x)) <>=> (c g.ncs x <+> (c g.cs x)))) 
    <|> ((zero_g' <|> (g.cexp <=> L.zero))
(*HZ simplified  after discussion with SW*)
     (* <&> (((~! zero_f') <&> (f.cexp <>> L.zero)) <|>  *)
      (* (if List.length (List.unique (vars ff @ (vars gg))) > 1 then L.bot else L.top)) *)
     <&> ((c f.cs x <+> (c f.ncs x)) <>=> (c g.cs x <+> (c g.ncs x))))
    in return phi

(*
and eq ff gg =
 get >>= fun c ->
 let eq' = function
  | _, Zero -> is_zero ff
  | Zero, _ -> is_zero gg
  | Ord f, Ord g -> 
(* TODO: vars of ff ignored *)
   map (eqx (Ord f) (Ord g)) (vars gg) >>= fun eqxs ->
   eq f.exp g.exp >>= fun eq_exp ->
   let eq_nz = (L.big_and eqxs) <&> (f.cexp <=> g.cexp) <&> 
    (is_pos f.cexp <->> eq_exp) <&> (f.c0 <=> g.c0) in
   (is_zero ff $<->$ (is_zero gg)) $&$ (nm (is_zero ff) $->$ (return eq_nz))
 in cache_m c.ht_eq eq' (ff,gg)

and eqx ff gg x =
 match ff,gg with
  | _, Zero -> is_zero ff
  | Zero, _ -> is_zero gg
  | Ord f, Ord g ->
   con x (mult f.cexp f.exp) >>= fun con_f ->
   con x (mult g.cexp g.exp) >>= fun con_g ->
   eqx f.exp g.exp x >>= fun eqx_exp ->
   let phi = (con_f <<->> con_g) <&> (con_f <->> eqx_exp)
    <&> (~! con_f <->> ((c f.cs x) <=> (c g.cs x)))
    <&>  ((c f.ncs x) <=> (c g.ncs x)) 
   in return phi
*) 
and gt f g =
 get >>= fun c ->
 let gt' = function
  | ff, Zero -> return (is_gt_zero ff)
  | Zero, _ -> return L.bot
  | (Ord f) as ff, ((Ord g) as gg) ->
   geq ff gg >>= fun geq ->
   gt0 ff gg >>= fun gt0 ->
   return (geq <&> gt0)
  in 
 compatible f g >>= fun _ ->  
 cache_m c.ht_gt gt' (f,g)

and gt0 f g = match f,g with
  | ff, Zero -> return (is_gt_zero ff)
  | Zero, _ -> return L.bot
  | (Ord f) as ff, ((Ord g) as gg) ->
   geq0 f.exp g.exp >>= fun geq0_exp ->
   gt0 f.exp g.exp >>= fun gt0_exp ->
   return (
    (gt0_exp <&> is_pos f.cexp) <|>
    (geq0_exp <&> (f.cexp <>=> g.cexp) <&> (f.c0 <>> g.c0)) <|>
    ((g.cexp <=> L.zero) <&> (f.c0 <>> g.c0)))
;;

(* \omega ^ f  - truncates according to out degree *)
let omega f = 
 let rec trunc d = function 
  | Zero -> Zero 
  | Ord f ->
   if d = 0 then Zero else make f.cs (trunc (d-1) f.exp) f.cexp f.ncs f.c0
 in let f' = make [] f L.one [] L.zero in
 get >>= fun c -> return (trunc c.out_deg f')
;;

(* if-then-else with condition c for abstract ordinal expressions *)
let pad cs xs =
 let xs' = List.filter (fun x -> not (List.mem_assoc x cs)) xs in
 cs @ (List.map (fun x -> x,L.zero) xs')
;;

let expand o = 
 let rec expand xs = function
  | Zero -> Zero
  | Ord f -> 
   Ord {f with cs = pad f.cs xs;ncs=pad f.ncs xs; exp = expand xs f.exp}
 in expand (vars o) o

let rec ite c f g =
 if f = Zero && g = Zero then Zero else
  let expand = function Ord o -> o | _ -> make_o [] Zero L.zero [] L.zero in
  let f,g = expand f,expand g in
  let iteall cs cs' = 
   let ite l = List.map (fun (x,a) -> x,L.ite c (List.assoc x l) a) in
   let xs = List.map fst (cs@cs') in 
   ite (pad cs xs) (pad cs' xs) 
  in
  make (iteall f.cs g.cs) (ite c f.exp g.exp) (L.ite c f.cexp g.cexp)
   (iteall f.ncs g.ncs) (L.ite c f.c0 g.c0)
;;

let dup x = x,x

let store_p c =
 if not !(globals.cache) then return c else
 if (c = Logic.bot) || (c = Logic.top) then return c
 else
  get >>= fun s -> fresh_bool >>= fun b ->
  (Hashtbl.add s.ht_pvars b c; return b)
;;

let store_a c =
 if not !(globals.cache) then return c else
 if (c = Logic.zero) || (c = Logic.one) then return c
 else
  get >>= fun s -> fresh_arith >>= fun b ->
  (Hashtbl.add s.ht_avars b c; return b)
;;

let nadd ff gg =
 match ff, gg with
  | Zero, _ -> return (gg,gg)
  |_, Zero -> return (ff,ff)
  | _, Ord g when only_nat g -> return (dup (add_nat_coeffs g.ncs ff))
  |Ord f, Ord g ->
   let c0 = f.c0 <+> g.c0 in
   let ncs = combine (<+>) f.ncs g.ncs in
   let f',g' = f.exp, g.exp in
   (gt g' f') $&$ (return (is_pos g.cexp)) >>= store_p >>= fun g_gt_f ->
   (gt f' g') $&$ (return (is_pos f.cexp)) >>= store_p >>= fun f_gt_g ->
   let h = 
       ite (f.cexp <=> L.zero) g.exp  
       (ite (g.cexp <=> L.zero) f.exp
       (ite f_gt_g f' (ite g_gt_f g' (omax f' g')))) in
   let hc =
       L.ite (f.cexp <=> L.zero) g.cexp 
       (L.ite (g.cexp <=> L.zero) f.cexp
       (L.ite f_gt_g (f.cexp <+> L.one) 
       (L.ite g_gt_f (g.cexp <+> L.one) (f.cexp <+> g.cexp)))) in
   let k = ite f_gt_g f' g' in
   let kc = L.ite f_gt_g f.cexp g.cexp in
   let xs = List.unique ((vars ff)@(vars gg)) in
   let ucf x = x, (c f.cs x) <+> (c g.cs x) in
   let lcf x =
    conw x g >>= fun cg ->
    conw x f >>= fun cf ->
    let t x = L.ite cg L.zero L.one in
    let s x = L.ite cf L.zero L.one in
    return (x, Logic.max ((s x)<*>(c f.cs x)) ((t x)<*>(c g.cs x))) 
   in
   map lcf xs >>= fun lcs ->
    
   let eat g x =
    conw x g >>= fun cg ->
    let t x = L.ite cg L.zero L.one in
    return (t x <*> c g.cs x)
   in
   let nat f = 
    let cs = f.cexp::List.map snd f.cs in
    Logic.big_and (List.map (fun c -> c <=> Logic.zero) cs)
   in
   let u1 = make f.cs f.exp f.cexp ncs c0 in
   let u2 = make g.cs g.exp g.cexp ncs c0 in
   map (fun (x,c) -> eat g x >>= fun d -> eat f x >>= fun e ->
    return (x,c <+> d <+> e)) ncs >>= fun ncs2 ->
   map (fun (x,_) -> return (x,Logic.zero)) f.cs >>= fun zs ->
   let u3 = make zs h hc ncs2 c0 in
   let u = ite (nat g) u1 (ite (nat f) u2 u3) in

   let l = make lcs k kc ncs c0 in
   return (u,l)
;;

let nadd f g =
 let t = Unix.gettimeofday () in
 compatible f g >>= fun _ ->
 nadd f g >>= fun r ->
 t_nadd := !t_nadd +. (Unix.gettimeofday () -. t);
 return r
;;

let rec at_most_one = function
 | [] -> Logic.top
 | f::fs -> 
  ((f <>> Logic.zero) <->> Logic.big_and (List.map ((<=>) Logic.zero) fs))
    <&> at_most_one fs
;;

(*HZ: this function could take sx and tx into account *)
let unary cs cns = 
 Logic.big_and (List.map ((<=>) Logic.zero) (List.map snd cs)) <&>
 at_most_one (List.map snd cns)
;;

(* f + g *) 
let add ff gg =
(* print_inter "add f " ff; print_inter "add g " gg; *)
 match ff, gg with
  | Zero, _ -> return (dup gg)
  | _, Zero -> return (dup ff)
 (* unsound if f = y and g = x + y?*)
  (* | Ord f, _ when is_mono f ->  *)
   (* return (dup (let x,a = mono f in add_std_coeff x a gg)) *)
  (*| Ord f, Ord g when (only_std f) && (is_mono g) -> 
   return (dup (add_std_coeffs f.cs (make_mono_std g)))*)
  | Ord f, Ord g ->
   let m0, m1 = return L.zero, return L.one in
   let t x = iteM (nm (conw x g)) m1 m0 in
   let s x = iteM (nm(conw x f)) m1 m0 in
   (* upper bound *)

   (gt g.exp f.exp) $&$ (return (is_pos g.cexp)) >>= store_p >>= fun g_gt_f ->
   (gt f.exp g.exp) $&$ (return (is_pos f.cexp)) >>= store_p >>= fun f_gt_g ->

   let cf x = 
    s x >>= fun sx -> 
    t x >>= fun tx ->
    let bug = L.ite (unary f.cs f.ncs) (tx<*>(c f.ncs x)) Logic.zero in
    let a =(sx<*>tx<*>(c f.cs x))<+>bug<+>(tx<*>(c g.cs x)) in
    let b =(sx<*>(c f.cs x)) in
    return (x,L.ite g_gt_f a (L.ite f_gt_g b (c f.cs x <+> c g.cs x) (*(max a b)*)))
   in
   let ncf x = 
    t x >>= fun tx ->
    let bug = L.ite (unary f.cs f.ncs) Logic.zero (tx<*>(c f.ncs x))in
    let a = c g.ncs x <+> bug in
    let b = (tx<*>(c f.ncs x))<+>(tx<*>(c g.cs x)) <+> (c g.ncs x) in
    return (x,L.ite g_gt_f a (L.ite f_gt_g b (c f.ncs x <+> c g.ncs x)(*(max a b)*)))
   in
   let xs = List.unique ((vars ff)@(vars gg)) in
   map cf xs >>= fun ucs ->
   map ncf xs >>= fun uncs ->
   let h =
       ite (f.cexp <=> L.zero) g.exp
       (ite ((g.cexp <=> L.zero) <|> f_gt_g) f.exp
       (ite g_gt_f g.exp (omax f.exp g.exp))) in
   let hc =
       L.ite (f.cexp <=> L.zero) g.cexp
       (L.ite (g.cexp <=> L.zero) f.cexp
       (L.ite f_gt_g (f.cexp <+> L.one)
       (L.ite g_gt_f g.cexp (f.cexp <+> g.cexp)))) in
   let c0 = (L.ite ((g.cexp <>> Logic.zero) <&> (is_gt_zero g.exp)) Logic.zero f.c0) <+> g.c0 in
   let u = make ucs h hc uncs c0 in
   (*lower bound*)
   let xs_g = vars gg in
   let cs_new = List.filter (fun (x,_) -> not (List.mem x xs_g)) f.ncs in
   let hh = Ord {g with cs = cs_new@g.cs} in
  (* print_inter "ff" ff; *)
  (* print_inter "gg" gg; *)
  (* print_inter "hh" hh; *)

   let l = ite f_gt_g ff hh in
   (* let l = ite g_gt_f gg ff in    *)
(*   print_inter "gives u " u;*)
   return (u,l)
;;

let add f g =
 let t = Unix.gettimeofday () in
 compatible f g >>= fun _ ->
 add f g >>= fun r ->
 t_add := !t_add +. (Unix.gettimeofday () -. t);
 return r
;;

let make_ord_var x = make [x,L.one] Zero L.zero [x,L.zero] L.zero
let make_var x     = make [x,L.zero] Zero L.zero [x,L.one] L.zero
let ito b = Logic.ite b Logic.one Logic.zero
let make_bool_var b x = make [x,ito b] Zero L.zero [x, ito (L.neg b)] L.zero

let fst_m = return <.> fst;;
let snd_m = return <.> snd;;

let rec compose d os = function
 | Zero -> return (Zero, Zero)
 | Ord o ->
  let vu = false in
  let vl = false in
  if vu || vl then print_inter (d ^ "COMPOSE: ") (Ord o);
  let us,ls = List.unzip os in
  let mult_all = List.map2 (fun t (_,a) -> mult a t) in
  (* upper bound *)
  (* let us = List.map (fun u -> ite (is_var u) (make_mono_std u) u) us in *)
  let ucs = List.map fst (mult_all us o.cs) in
  if vu then List.iter (print_inter (d ^ "after mult: ")) ucs;
  foldl (fun u u' -> add u u' >>= fst_m) Zero ucs >>= fun u ->
  if vu then print_inter (d ^ "after std addition: ") u;
  compose (d ^ " ") os o.exp >>= fun (uexp,lexp) ->
  if vu then print_inter (d ^ "uexp: ") uexp;
  omega uexp >>= fun ue' -> let ue = fst (mult o.cexp ue') in
  if vu then print_inter (d ^ "w^{uexp}: ") ue;
  add u ue >>= fst_m >>= fun u ->
  if vu then print_inter (d ^ "after exp add: ") u;
  let uncs = List.map fst (mult_all us o.ncs) in
  foldl (fun u u' -> nadd u u' >>= fst_m) Zero uncs >>= fun u' ->
  if vu then print_inter (d ^ "nadd yields: ") u';
  nadd u u' >>= fst_m >>= fun u -> 
  if vu then print_inter (d ^ "after adding nadd: ") u;
  let u = const_add o.c0 u in
  if vu then print_inter (d ^ "final upper bound: ") u;
  (* lower bound *)
  let lcs = List.map snd (mult_all ls o.cs) in
  foldl (fun l l' -> add l l' >>= snd_m) Zero lcs >>= fun l ->
  if vl then print_inter (d ^ "after std addition: ") l;
  omega lexp >>= fun le' -> let le = snd (mult o.cexp le') in
  if vl then print_inter (d ^ "exponent: ") le;
   (*HZ changed order*)
  (* add l le >>= snd_m >>= fun l -> *)
  add le l >>= snd_m >>= fun l ->
  if vl then print_inter (d ^ "after adding exponent: ") l;
  let lncs = List.map snd (mult_all ls o.ncs) in
  foldl (fun l l' -> nadd l l' >>= snd_m) Zero lncs >>= fun l' ->
  if vl then print_inter (d ^ "nat add yields: ") l';
  nadd l l' >>= snd_m >>= fun ll ->
  if vl then print_inter (d ^ "together: ") ll;
  let l = const_add o.c0 ll in
  if vl then print_inter (d ^ "final lower bound: ") l;
  (* return pair *)
  return (u,l)
 ;;

let output_degree_conditions (u,l) =
 let conds f =
  get >>= fun c ->
  if depth f < c.out_deg then return ()
  else
   let rec cexps = function Zero -> [] | Ord f -> f.cexp :: (cexps f.exp) in 
   map store_a (cexps f) >>= fun vs ->
   let vs = List.map (fun a -> (a <=> L.zero)) vs in
(*HZ? big_or -> big_and? this requires increasing -od flag*)
   set {c with p_constraints = (c.p_constraints <&> (Logic.big_or vs))}
 in project conds (u,l)
;;

let interpret_with_args os o =
 let t = Unix.gettimeofday () in
 compose "" os o >>= fun r ->
 t_compose := !t_compose +. (Unix.gettimeofday () -. t);
 output_degree_conditions r >>
 return r
;;

(* add coefficients of same variables *)
let rec unique = function
   [] -> []
 | (x,a) :: cs when List.mem_assoc x cs ->
  let ((_,a') as p) = List.find (fun (x',_) -> x' = x) cs in
  unique ((x,a <+> a') :: (List.remove p cs))
 | (x,a) :: cs -> (x,a) :: (unique cs)
;;

let rec substitute_vars xs = function
 | Zero -> Zero
 | Ord f ->
  let d = List.zip (List.map fst f.cs) xs in
  let sub = unique <.> (List.map (fun (x,a) -> List.assoc x d,a)) in
  make (sub f.cs) (substitute_vars xs f.exp) f.cexp (sub f.ncs) f.c0
;;

let side_conditions () =
 let p v a = Format.printf "%a <-> %a\n%!" L.fprintf_p v L.fprintf_p a in
 let f ht =
  Hashtbl.fold (fun _ (v,a) phi -> 
   if (v = L.top) || (v = L.bot) then phi
   else ((*p v a;*) phi <&> (v <<->> a))
  ) ht Logic.top
 in
 let f' cmp ht = Hashtbl.fold (fun c v p -> p <&> (cmp v c)) ht Logic.top in
 get >>= fun c ->
 return ((f c.ht_eq) <&> (f c.ht_geq) <&> (f c.ht_gt) <&> (f c.ht_con) 
 <&> (f c.ht_zero) <&> (f' (<<->>) c.ht_pvars) <&> (f' (<=>) c.ht_avars)
 <&> c.p_constraints <&> c.p_compatible)
;;
