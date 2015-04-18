(* $Id: pb2bdd.ml,v 1.10 2013/12/12 10:08:22 hzankl Exp $ *)

(* Copyright 2013 Harald Zankl
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

(*** MODULES (1) **************************************************************)
module F = Format;;
module H = Hashtbl;;

(*** OPENS (1) ****************************************************************)
open Util;;

(*** GLOBALS ******************************************************************)
type var_order = INC | DEC;;
let var_order = ref DEC;;
let po2 = ref false;;
let dv = ref false;;
let bdd = ref 1;;

(*** TYPES (1) ****************************************************************)
type coeff = Int64.t;;
let fprintf_coeff fmt coeff = F.fprintf fmt "%s" (Int64.to_string coeff);;
type var = Logic.p;;
let fprintf_var fmt var = F.fprintf fmt "%a" Logic.fprintf_p var;;

let (|<|) x y = x < y;;
let (|<=|) x y = x <= y;;
let (|-|) x y = Int64.sub x y;;
let (|+|) x y = Int64.add x y;;

let maxv x y = max x y;;
let minv x y = min x y;;

(*** MODULES (2) **************************************************************)
(* module S = SmtFormula;; *)
(* module P = Parsec.StringParser;; *)

module Interval = struct
type icoeff = Minf | Inf | Coeff of coeff;;
type t = icoeff * icoeff;;

let minus_one = Coeff Int64.minus_one;;
let zero = Coeff Int64.zero;;
let minf = Minf;;
let inf = Inf;;

let max_val a b = match (a,b) with
 | Minf,b -> b
 | a,Minf -> a 
 | Coeff a,Coeff b    -> Coeff (maxv a b)
;;

let min_val a b = match (a,b) with
 | Inf,b -> b
 | a,Inf -> a
 | Coeff a, Coeff b   -> Coeff (minv a b)
;;

let add c = function
 | Minf -> Minf
 | Inf -> Inf
 | Coeff a -> Coeff (a |+| c)
;;

let add c i = Pair.map (add c) i;;

let merge l r = (max_val (fst l) (fst r),min_val (snd l) (snd r));;

let (=) l r = l = r;;

let mem k = function
 | Minf,Coeff b -> k |<=| b
 | Coeff a, Inf -> a |<=| k
 | Coeff a, Coeff b -> a |<=| k && k |<=| b
;;

let fprintf fmt = function
 | (Minf,Coeff a) -> F.fprintf fmt "(-&,%a]" fprintf_coeff a
 | (Coeff a,Inf) -> F.fprintf fmt "[%a,&)" fprintf_coeff a
 | (Coeff a,Coeff b) -> F.fprintf fmt "[%a,%a]" fprintf_coeff a fprintf_coeff b
;;

(*debug *)
(*
let mem k i = 
 let r = mem k i in
 let _ = F.printf "k: %a, i: %a, mem: %b@\n" fprintf_coeff k fprintf i r in
 r
*)
end


module Bdd = struct
(*** TYPES (3) *****************************************************************)
type npbc = (coeff * var) list * coeff;;
let fprintf_cx fmt (c,x) = 
 F.fprintf fmt "%a%a" fprintf_coeff c fprintf_var x
;;
let fprintf_pb fmt (lhs,k) = 
 F.fprintf fmt "@[%a <= %a;@]" (List.fprintf fprintf_cx " + ") lhs fprintf_coeff k
;;

type node = var * coeff * Interval.t;;

type 'a bdd = True | False | Node of ('a bdd * 'a * 'a bdd);;

(*** FUNCTIONS (3) *************************************************************)

let mk_false = False;;
let mk_true = True;;

let false_intv = (Interval.minf,Interval.minus_one);;
let true_intv  = (Interval.zero,Interval.inf);;

(*just for printing*)
let fprintf_node fmt (var,coeff,intv) =
 F.fprintf fmt "(%a,%a,%a)" fprintf_var var fprintf_coeff coeff Interval.fprintf intv
;;

let fprintf_root fmt = function
 | True -> F.fprintf fmt "(T,%a)" Interval.fprintf true_intv
 | False -> F.fprintf fmt "(F,%a)" Interval.fprintf false_intv
 | Node(_,n,_) -> fprintf_node fmt n
;;

let rec fprintf_edges fmt d tbl = function
 | True -> ()
 | False -> () 
 | Node (l,n,r) as bdd ->
  if H.mem tbl bdd then () else (
  let _ = H.add tbl bdd () in
  F.fprintf fmt "%s%a -1> %a@\n" d fprintf_node n fprintf_root l;
  fprintf_edges fmt (d^" ") tbl l;
  F.fprintf fmt "%s%a -0> %a@\n" d fprintf_node n fprintf_root r;
  fprintf_edges fmt (d^ " ") tbl r);
;;

let fprintf fmt = function
 | True -> F.fprintf fmt "True"
 | False -> F.fprintf fmt "False"
 | bdd -> fprintf_edges fmt "" (H.create 512) bdd
;;

let size bdd = 
 let tbl = H.create 512 in
 let rec size bdd = 
  if H.mem tbl bdd then 0 else 
  let _ = H.add tbl bdd () in
  match bdd with
   | False -> 1
   | True -> 1
   | Node(l,_,r) as bdd -> size l + size r + 1
 in
 size bdd 
;;

let interval = function
 | False -> false_intv
 | True -> true_intv
 | Node(_,(v,c,i),_) -> i
;;

let mk_empty k = if k |<| Int64.zero then mk_false else mk_true;;

(*construct non-reduced bdd*)
let rec bdd0 = function
 | ([],k) -> mk_empty k 
 | ((c,x)::xs,k) ->
  let l = bdd0 (xs,k |-| c) in
  let r = bdd0 (xs,k) in
  let i = Interval.merge (Interval.add c (interval l)) (interval r) in
  Node (l,(x,k,i),r)
;;

let strange_find tbl x k =
 if Hashtbl.mem tbl x then
  let cs = Hashtbl.find tbl x in
  List.find_option (fun (i,_) -> Interval.mem k i) cs
 else
  None
;;
 
let update tbl x r =
 let cs = if Hashtbl.mem tbl x then Hashtbl.find tbl x else [] in
 let _ = Hashtbl.replace tbl x (r::cs) in
 r
;;

let mk_empty_intv k =
 if k |<| Int64.zero then (false_intv,mk_false) else (true_intv,mk_true)
;;

(*construct reduced bdd*)
(*Algorithm 1*)
let bdd1 pb =
 let tbl (*: coeff * var -> (interval * node bdd) list*) = Hashtbl.create 512 in
 let rec bdd = function
  | ([],k) -> mk_empty_intv k
  | ((c,x)::xs,k) as pb ->
   match strange_find tbl (c,x) k with 
    | Some (i,bdd) -> (i,bdd)
    | None -> match pb with
     | ((c,x)::xs,k) -> 
      let (li,l) = bdd (xs,k|-|c) in
      let (ri,r) = bdd (xs,k) in
      let i = Interval.merge (Interval.add c li) ri in
       (* let _ = F.printf "... var: %a, k: %a, l: %a, r: %a, int: %a@\n"  *)
        (* fprintf_var x fprintf_coeff k fprintf_root l fprintf_root r Interval.fprintf i in *)
      let bdd = if Interval.(=) li ri then l else Node(l,(x,k,i),r) in
      update tbl (c,x) (i,bdd)
 in snd (bdd pb)
;;

(*drop repeated variables along a path*)
let drop_vars bdd = 
 let rec ddv ds = function 
  | True -> True
  | False -> False
  | Node(l,(x,k,i),r) ->
   try match List.assoc x ds with
    | True -> l
    | False -> r
   with | Not_found -> 
   Node(ddv ((x,True)::ds) l,(x,k,i),ddv ((x,False)::ds) r)
 in ddv [] bdd
;;

(*
(*towards construct reduced bdd w/o duplicated variables *)
let bdd2 pb =
 let tbl (*: var -> (interval * node bdd) list*) = Hashtbl.create 512 in
 let rec bdd ds = function
  | ([],k) -> mk_empty_intv k
  | ((c,x)::xs,k) as pb ->
   try 
    match List.assoc x ds with
     | True  -> let (li,l) = bdd ds (xs,k|-|c) in
                let (ri,_) = bdd ds (xs,k) in
                update tbl x ((Interval.merge (Interval.add c li) ri),l)
     | False -> let (li,_) = bdd ds (xs,k|-|c) in
                let (ri,r) = bdd ds (xs,k) in
                update tbl x ((Interval.merge (Interval.add c li) ri),r)
  with | Not_found -> 
    match strange_find tbl x k with 
     | Some (i,bdd) -> (i,bdd)
     | None -> match pb with
      | ((c,x)::xs,k) -> 
       let (li,l) = bdd ((x,True)::ds) (xs,k|-|c) in
       let (ri,r) = bdd ((x,False)::ds) (xs,k) in
       let i = Interval.merge (Interval.add c li) ri in
        (* let _ = F.printf "... var: %a, k: %a, l: %a, r: %a, int: %a@\n"  *)
         (* fprintf_var x fprintf_coeff k fprintf_root l fprintf_root r Interval.fprintf i in *)
       let bdd = if Interval.(=) li ri then l else Node(l,(x,k,i),r) in
       update tbl x (i,bdd)
 in snd (bdd [] pb)
;;
*)

(*construct reduced bdd w/o duplicated variables *)
let bdd2 pb =
 let tbl (*: coeff * var * ds -> (interval * node bdd) list*) = Hashtbl.create 512 in
 let rec bdd d ds = function
  | ([],k) -> mk_empty_intv k
  | ((c,x)::xs,k) as pb ->
   try match List.assoc x ds with
    | True -> let (li,l) = bdd (d^".") ds (xs,k|-|c) in
              let (ri,_) = bdd (d^".") ds (xs,k) in
              update tbl (c,x,ds) ((Interval.merge (Interval.add c li) ri),l)
    | False -> let (li,_) = bdd (d^".") ds (xs,k|-|c) in
               let (ri,r) = bdd (d^".") ds (xs,k) in
              update tbl (c,x,ds) ((Interval.merge (Interval.add c li) ri),r)
   with | Not_found -> 
   match strange_find tbl (c,x,ds) k with 
    | Some (i,bdd) -> (i,bdd)
    | None -> match pb with
     | ((c,x)::xs,k) -> 
       (* let _ = F.printf "%svar: %a, k: %a@\n@?" d fprintf_var x fprintf_coeff k in *)
      let (li,l) = bdd (d^".") ((x,True)::ds) (xs,k|-|c) in
      let (ri,r) = bdd (d^".") ((x,False)::ds) (xs,k) in
      let i = Interval.merge (Interval.add c li) ri in
       (* let _ = F.printf "%sint:%a, l: %a, li: %a r: %a, ri: %a@\n@?" d *)
        (* Interval.fprintf i fprintf_root l Interval.fprintf li fprintf_root r Interval.fprintf ri  *)
        (* in *)
      (* let bdd = if Interval.(=) li ri then l else Node(l,(x,k,i),r) in *)
      (* let bdd = if l = r then l else Node(l,(x,k,i),r) in *)
      let bdd = Node(l,(x,k,i),r) in
      update tbl (c,x,ds) (i,bdd)
 in snd (bdd "." [] pb)
;;

end

open Logic.Operators;;
let (>>=) = Logic.(>>=);;
let return = Logic.return;;

let bdd2sat bdd = 
 let fvars = H.create 512 in
 let cache = H.create 512 in
 let rec bdd2sat acc = function
  | Bdd.False -> return acc
  | Bdd.True -> return acc
  | Bdd.Node(l,(x,a,i),r) as bdd ->
   if H.mem cache bdd then return acc else
   let _ = H.add cache bdd () in
   Logic.cache_bool fvars bdd >>= fun n ->
   Logic.cache_bool fvars l >>= fun t ->
   Logic.cache_bool fvars r >>= fun f ->
   bdd2sat acc l >>= fun acc -> 
   bdd2sat acc r >>= fun acc ->
   return ((f <|> (~!n))::(t <|> (~!x) <|> (~!n))::acc)
  in
  bdd2sat [] bdd >>= fun b ->
  Logic.cache_bool fvars Bdd.False >>= fun f ->
  Logic.cache_bool fvars Bdd.True >>= fun t ->
  Logic.cache_bool fvars bdd >>= fun vb ->
  return (Logic.big_and (vb::t::~!f::b))
;;

let drop_vars bdd = if !dv then Bdd.drop_vars bdd else bdd;;
let pb2bdd pb = match !bdd with
 | 0 -> Bdd.bdd0 pb
 | 1 -> Bdd.bdd1 pb
 | 2 -> Bdd.bdd2 pb
;;

let pb2sat pb = 
  (* let _ = F.printf "@[<1>pb:@\n%a@]@\n" Bdd.fprintf_pb pb in *)
 let bdd = pb2bdd pb in
  (* let _ = F.printf "@[<1>bdd:@\n%a@]@\n" Bdd.fprintf bdd in *)
  (* let _ = Debug.debug (F.sprintf "bdd (%d nodes)" (Bdd.size bdd)) in *)
  (* let _ = Debug.debug2 (F.fprintf F.str_formatter "@[<1>bdd@\n%a@]" Bdd.fprintf bdd) in *)
 let bdd = drop_vars bdd in
  (* let _ = Debug.debug (F.sprintf "bdd (%d nodes)" (Bdd.size bdd)) in *)
  (* let _ = Debug.debug2 (F.fprintf F.str_formatter "@[<1>bdd@\n%a@]" Bdd.fprintf bdd) in *)
 bdd2sat bdd >>= fun sat ->
  (* let _ = F.printf "@[<1>sat:@\n%a@]@\n" Logic.fprintf_p sat in *)
 return sat
;;

(*
let pbcs2sat pbcs = 
 Logic.Monad.sequence (List.map pb2sat pbcs) >>= fun cs ->
 return (Logic.big_and cs)
;;
 
let solve ?(aux=Logic.top) pbcs = 
 pbcs2sat pbcs >>= fun sat ->
 Logic.solve (aux<&>sat)
;;
*)


(*normalize PB*)
module S = SmtFormula;;

(* transform "sum ci xi >= k" with ci in Int into "sum pi xi <= k" with pi in Nat*)
let const2int64 (S.Const x) = x;;

let ge2le tbl pbc = 
 let split_mul = function 
  | (S.Mul [S.Const c;S.Vara x]) -> (c,S.Vara x) 
  | (S.Mul [S.Vara x;S.Const c]) -> (c,S.Vara x)
  | (S.Vara x) -> (Int64.one,S.Vara x)
 in
 let normalize_sum = function
  | S.Add(sum) -> sum
  | sum -> [sum]
 in
 match pbc with
 | S.Ge(sum,S.Const k) -> 
  let sum = normalize_sum sum in
  Logic.Monad.map (fun s -> 
   let (c,x) = split_mul s in
   Logic.cache_bool tbl x >>= fun x ->
   return (Int64.neg c,x)) sum >>= fun sum ->
   return (sum,Int64.neg k)
 | S.Ge(S.Const k,sum) -> 
  let sum = normalize_sum sum in
  Logic.Monad.map (fun s ->
   let (c,x) = split_mul s in
   Logic.cache_bool tbl x >>= fun x ->
   return (c,x)) sum >>= fun sum ->
   return (sum,k)
 | _ -> failwith (F.sprintf "not matched: %s@\n" (S.b_to_string pbc) )
;;

let normalize_comparison tbl phi = ge2le tbl phi;;

let normalize_coefficients tbl (cs,k) = 
 List.foldl (fun acc (c,x) ->
  Logic.cache_bool tbl x >>= fun y ->
  acc >>= fun (cs,k') ->
  return (if (c >= Int64.zero) then ((c,x)::cs,k')
          else ((Int64.neg c,y)::cs,k' |-| c)))
 (return ([],k))
 cs
;; 

let complement_sc tbl = 
 H.fold (fun k v acc -> acc <&> (k <|> v) <&> ((~! k) <|> (~! v))) tbl Logic.top;;

(*testing*)
(*
open Bdd;;
let test_bdd () =
let pb1 = ([(3,1);(2,2);(4,3)],5) in
let pb2 = ([(3,1);(2,2);(4,1)],5) in
let pb3 = ([(3,1);(2,2);(4,3)],7) in
let pb4 = ([(3,1);(2,2);(4,1)],7) in

let pb5 = ([(1,1);(1,2);(2,1)],2) in

let pb = pb5 in
F.printf "@[<1>pbc:@\n@[%a@]@]@\n" fprintf_pb pb;;;
F.printf "@[<1>full bdd:@\n@[%a@]@]@\n" fprintf (bdd pb);
F.printf "@[<1>reduced bdd:@\n@[%a@]@]@\n" fprintf (bdd2 pb);
F.printf "@[<1>reduced bdd;remove repeated variables afterwards:@\n@[%a@]@]@\n"
 fprintf (drop_vars (bdd2 pb));
F.printf "@[<1>reduced bdd with removing repeated variables:@\n@[%a@]@]@\n"
 fprintf (bdd2 pb);
in
*)

(*
let test () = 
 Logic.run (
 Logic.fresh_bool >>= fun x1 ->
 Logic.fresh_bool >>= fun x2 ->
 Logic.fresh_bool >>= fun x3 ->
 (* let pb1 = ([(3,x1);(2,x2);(4,x3)],5) in *)
 let pb1 = ([(1,x1);(1,x2)],1) in
 solve [pb1] >>= function
  | None -> return (F.printf "UNSAT@\n")
  | Some ass -> 
     Logic.eval_p x1 ass >>= fun v1 ->
     Logic.eval_p x2 ass >>= fun v2 ->
     Logic.eval_p x3 ass >>= fun v3 ->
    F.printf "@[<1>SAT@\n%a : %b, %a : %b,%a : %b@]\n" 
     Logic.fprintf_p x1 v1
     Logic.fprintf_p x2 v2
     Logic.fprintf_p x3 v3;
    return ()
 )
in

test ();;
*)

let val_of b = if b then Logic.Number.of_int 1 else Logic.Number.of_int 0;;

let massage smt2pb_var_tbl ass = 
 H.fold (fun (S.Vara k) v acc -> Logic.eval_p v ass >>= fun vx -> acc >>= fun acc ->
         return ((k,val_of vx)::acc)) smt2pb_var_tbl (return []) >>= fun aa ->
 return (aa,[])
;;

let order (sum,k) = match !var_order with
  | INC -> (List.sort Pervasives.compare sum,k)
  | DEC -> (List.sort (fun x y -> ~-1* Pervasives.compare x y) sum,k)
;;

let power_of_two_coeff (c,x) = 
 let one = Int64.of_int 1 in
 let two = Int64.of_int 2 in
 let rec bits c = 
  if c = Int64.zero then []
  else Int64.rem c two::bits (Int64.div c two)
 in
 let rec po2 c = function
  | [] -> []
  | b::bs when b = one -> (c,x)::po2 (Int64.mul c two) bs
  | _::bs -> po2 (Int64.mul c two) bs
 in
 let cs = po2 one (bits c) in
 cs
;;

let power_of_two (sum,k) = 
 if !po2 then (List.flat_map power_of_two_coeff sum,k) else (sum,k)
;;

(*PB2CNF*)
let pb2cnf smt2pb_var_tbl flip_var_tbl phi =
 normalize_comparison smt2pb_var_tbl phi >>= fun pb ->
  (* let _ = Debug.debug2 (F.fprintf F.str_formatter "pb1: %a@\n" Bdd.fprintf_pb pb) in *)
 normalize_coefficients flip_var_tbl pb >>= fun pb ->
  (* let _ = Debug.debug2 (F.fprintf F.str_formatter "pb2: %a@\n" Bdd.fprintf_pb pb) in *)
  (* let _ = F.printf "sc: %a@\n" Logic.fprintf_p sc in *)
  (* let _ = Debug.debug2 (F.fprintf F.str_formatter "pb_in: %a@\n" Bdd.fprintf_pb pb) in *)
 let pb = power_of_two pb in
  (* let _ = Debug.debug2 (F.fprintf F.str_formatter "pb_po2: %a@\n" Bdd.fprintf_pb pb) in *)
 let pb = order pb in
  (* let _ = Debug.debug2 (F.fprintf F.str_formatter "pb_ordered: %a" Bdd.fprintf_pb pb) in *)
 pb2sat pb
;;

let eval_pb ass pb = 
 Logic.eval_a ass pb

let solve pbcs = 
 let smt2pb_var_tbl = H.create 512 in
 let flip_var_tbl = H.create 512 in
 Logic.Monad.map (pb2cnf smt2pb_var_tbl flip_var_tbl) pbcs >>= fun cnfs ->
 let sc = complement_sc flip_var_tbl in
  (* let _ = Debug.debug2 (F.fprintf F.str_formatter "pbf: %a@\n" Logic.fprintf_p sc) in *)
 let cnf = Logic.big_and (sc::cnfs) in
  (* let _ = Debug.debug2 (F.fprintf F.str_formatter "solving: %a@\n" Logic.fprintf_p cnf) in *)
  let _ = Debug.debug "internal: cnf generated" in
  let _ = if !Debug.on then Logic.set_print_stat () else () in
 Logic.solve ~cnf:true cnf >>= function
  | None -> return None
  | Some ass -> 
   let _ = Debug.debug "internal: cnf solved" in
   (* let _ = F.printf "ass: %a@\n" Logic.fprintf_assignment ass in *)
   massage smt2pb_var_tbl ass >>= fun ass ->
 return (Some ass)
;;
 
 (*
let test () = 
Logic.run (
 let s1 = S.Mul[S.Const Int64.one;S.Vara "1"] in
 let s2 = S.Mul[S.Const Int64.one;S.Vara "2"] in
 let s3 = S.Mul[S.Const (Int64.of_int 2);S.Vara "3"] in
 let s4 = S.Mul[S.Const (Int64.of_int 2);S.Vara "4"] in
 let s5 = S.Mul[S.Const (Int64.of_int 4);S.Vara "5"] in
 let phi = S.Ge(S.Const (Int64.of_int 6),S.Add[s1;s2;s3;s4;s5]) in
 solve [phi]
)
;;

test ();;
*)
