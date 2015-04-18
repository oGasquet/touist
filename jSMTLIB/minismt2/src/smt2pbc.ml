(* $Id: smt2pbc.ml,v 1.24 2013/12/12 10:08:23 hzankl Exp $ *)

(* Copyright 2013 Sarah Winkler
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
module N = Logic.Number;;
module S = SmtFormula;;
module F = Format;;

(*** OPENS (1) ****************************************************************)
open Util;;
open Logic.Operators;;
open SmtFormula;;

(*** TYPES ********************************************************************)
type context = {
 (* arithmetic variable mapped to its binary PB variable representation *)
 avar_tbl : (S.var,S.a) H.t;
 (* uniform names for propositional variables *)
 bvar_tbl : (S.var,S.var) H.t;
 (* vars for vars in cnf *)
 cnf_vars : (String.t, Logic.p) H.t;
 (* input bits *)
 ib : int;
 (* caches for distribution results *)
 distr_a_cache: (S.a,S.a  * S.b list) H.t;
 distr_b_cache: (S.b,S.b  * S.b list) H.t;
 (* caches for linearization results *)
 linearize_a_cache: (S.a,S.a) H.t;
 linearize_b_cache: (S.b,S.b) H.t;
 (* mapping arithmetic variables: S.var to L.var *)
 logic_avar : (String.t, L.a) H.t;
 (* fresh variable counter *)
 vcount : int ref;
 (* generated PB constraints *)
 pb_cs : S.b list;
 (* pb solver command *)
 pb_solver : string;
 (* contains x*y mapped to z (for linearization) *) 
 vmult : (S.var * S.var, S.var) H.t;
};;

(*** GLOBALS ******************************************************************)
let ctx = {
 avar_tbl = H.create 512;
 bvar_tbl = H.create 512;
 cnf_vars = H.create 512;
 ib = 2;
 distr_a_cache = H.create 512;
 distr_b_cache = H.create 512;
 linearize_a_cache = H.create 512;
 linearize_b_cache = H.create 512;
 logic_avar = H.create 512;
 vcount = ref 1;
 pb_cs = [];
 pb_solver = "./gpw";
 vmult = H.create 512;
};;

let nnf_cache : (S.b,S.b) H.t = H.create 512;;
let negate_cache : (S.b,S.b) H.t = H.create 512;;

(*** MODULES (2) **************************************************************)
module Statex = struct type t = context end;;
module M = Util.Monad.Transformer.State (Statex) (Logic.Monad);;

(*** OPENS (2) ****************************************************************)
open M;;

(*** FUNCTIONS ****************************************************************)
let mk_ctx ib s = {ctx with ib = ib; pb_solver = s};;

let var_prefix = "x";;
let var_of_int i = var_prefix ^ (string_of_int i)
let fresh_a ctx = let x = Vara (var_of_int !(ctx.vcount)) in incr ctx.vcount;x
let fresha () = M.get >>= fun c -> return (fresh_a c)
let fresh_b ctx = let x = var_of_int !(ctx.vcount) in incr ctx.vcount;x
let freshb () = M.get >>= fun c -> return (fresh_b c)
let freshs n = map fresha (List.replicate n ())

let cache t f k =
 if H.mem t k then H.find t k
 else let v = f k in H.add t k v; v
;;

let cachem t f k =  
 if H.mem t k then M.return (H.find t k) 
 else (f k >>= fun v -> H.add t k v; return v)
;;

let h_foldm f h r = H.fold (fun k v a -> a >>= fun a' -> f k v a') h (return r) 

let is_const = function Const c -> true | _ -> false
let to_const = function Const c -> c | _ -> failwith "invalid input to_const"
let to_var = function Vara c -> c | _ -> failwith "invalid input to_var"
let const i = Const (Int64.of_int i)

let mk_sub bs = Sub bs
let mk_not b = Not b
let mk_and bb = And bb
let mk_or bb = Or bb
let mk_imp (b1,b2) = Implies (b1,b2)
let mk_iff bb = Iff bb
let mk_eq (a1,a2) = S.eq a1 a2
let mk_ge (a1,a2) = S.ge a1 a2
let mk_gt (a1,a2) = S.gt a1 a2

let s_mul =
 let rec mul c acc = function
  | [] -> if acc = [] then Const c 
          else if c <> Int64.one then Mul ((Const c)::acc)
          else if List.length acc = 1 then List.hd acc else Mul acc
  | (Mul xs)::ys -> mul c acc (xs @ ys)
  | (Const a)::ys -> mul (Int64.mul c a) acc ys
  | x::xs -> mul c (x::acc) xs
 in function
  | [] -> const 1
  | [a] -> a
  | al -> mul Int64.one [] al
;;

let s_add al =
 let rec add c acc = function
  | [] -> if acc = [] then Const c else
          if c = Int64.zero then Add acc else Add ((Const c)::acc)
  | (Add xs)::ys -> add c acc (xs @ ys)
  | (Const a)::ys -> add (Int64.add c a) acc ys
  | x::xs -> add c (x::acc) xs
 in if List.length al = 1 then List.hd al else add Int64.zero [] al
;;

let s_and al =
 if List.mem Bot al then Bot else
 match List.filter (fun b -> b <> Top) al with
  | [] -> Top
  | [a] -> a
  | al' -> And al'
;;

let s_or al =
 if List.mem Top al then Top else
 match List.filter (fun b -> b <> Bot) al with
  | [] -> Bot
  | [a] -> a
  | al' -> Or al'
;;

let add_constraint x = M.get >>= fun c -> M.set {c with pb_cs = x::c.pb_cs}
let add_constraints = iter add_constraint



(* -------------------------------------------------------------------------- *)
(* --- 1. arithmetic variables to binary representation --------------------- *)
(* -------------------------------------------------------------------------- *)

(* generate binary representation in k bits*)
let rec binvars ctx = function
 | i when i < 1 -> failwith "0 bit respresenation"
 | 1 -> fresh_a ctx
 | k -> s_add [Mul[const (Int.pow 2 (k-1)); fresh_a ctx]; 
  binvars ctx (k-1)]
;;
 
(* recursive replacement in formulas *)
let rec replace_pb v =
 M.get >>= fun c ->
 let to_binary _ = return (binvars c c.ib) in
 cachem c.avar_tbl to_binary v
and var2pb_a = function
 | Const a -> return (Const a)
 | Vara x -> replace_pb x
 | Add aa -> map var2pb_a aa >>= (return <.> s_add)
 | Sub aa -> map var2pb_a aa >>= (return <.> mk_sub)
 | Mul aa -> map var2pb_a aa >>= (return <.> s_mul)
 | Ite (b,a1,a2) -> 
  var2pb_b b >>= fun b' ->
  project var2pb_a (a1,a2) >>= fun (a1',a2') ->
  return (Ite(b',a1',a2'))
and var2pb_b = function
 | Not b -> var2pb_b b >>= (return <.> mk_not)
 | Or bb -> map var2pb_b bb >>= (return <.> mk_or)
 | And bb -> map var2pb_b bb >>= (return <.> mk_and)
 | Implies (b1,b2) -> project var2pb_b (b1,b2) >>= (return <.> mk_imp)
 | Iff bb -> map var2pb_b bb >>= (return <.> mk_iff)
 | Eq (a1,a2) -> project var2pb_a (a1,a2) >>= (return <.> mk_eq)
 | Ge (a1,a2) -> project var2pb_a (a1,a2) >>= (return <.> mk_ge)
 | Gt (a1,a2) -> project var2pb_a (a1,a2) >>= (return <.> mk_gt)
 | Varb x -> M.get >>= fun c -> cachem c.bvar_tbl (fun _ -> freshb ()) x 
  >>= fun x' -> return (Varb x')
 | b -> return b
;;

let replace_vars = var2pb_b

(* -------------------------------------------------------------------------- *)
(* --- 2. normalize arithmetic ---------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

(* select Add or Sub argument of list *)
let rec select_add =
 let rec select acc =  function
  | [] -> None
  | (Add aa) :: bb -> Some (s_add aa, s_mul (bb @ acc))
  | (Sub aa) :: bb -> Some (Sub aa, s_mul (bb @ acc))
  | a :: aa -> select (a::acc) aa
 in select []
;;

let replace_ite b a1 a2 =
 fresha () >>= fun x ->
 (*fresha () >>= fun neg_x ->*)
 let neg_x = Add[const 1; Mul[const (-1);x]] in
 let c = Iff[b; Eq(x,const 1)(*; Eq(neg_x,const 0)*)] in
 return (s_add[s_mul[x;a1]; s_mul[neg_x;a2]],[c])
;;

(* normalize arithmetic terms such that 
   - Subs are replaced by Adds
   - Muls occur below Adds
   - Ites are replaced *)
let rec distr_a a =
 let distr_a' = function
  | Add aa -> distr_a_all aa >>= fun (aa,c) -> (return (s_add aa, c))
  | Sub (a::aa) -> distr_a (s_add[a; s_mul [const (-1); s_add aa]])
  | Mul aa -> (
   distr_a_all aa >>= fun (aa',c) ->
   match select_add aa' with
    | Some (Add ss,r) -> 
     distr_a_all (List.map (fun x -> s_mul [x;r]) ss) >>= fun (aa,c') -> 
     return (s_add aa, c'@c)
    | Some (Sub ss,r) -> 
     let r = s_mul [const (-1); r] in
     distr_a_all (List.map (fun x -> s_mul [x;r]) ss) >>= fun (aa,c') -> 
     return (s_add aa, c'@c)
    | None ->  return (s_mul aa', c)
    | _ -> failwith "select_add: strange result")
  | Ite (b,a1,a2) -> 
   distr_b b >>= fun (b',c') ->
   replace_ite b' a1 a2 >>= fun (a, c) ->
   distr_a a >>= fun (a', c'') -> 
   return (a', c @ c' @ c'')
  | a -> return (a,[])
 in M.get >>= fun c -> cachem c.distr_a_cache distr_a' a
and distr_a_all aa = 
 map distr_a aa >>= fun aa' ->
 return (List.foldl (fun (aa,cc) (a,c) -> (a::aa,c@cc)) ([],[]) aa')
and distr_b b = 
 let distr_b' = function 
  | Not b -> distr_b b >>= fun (b',c) -> return (Not b',c)
  | Or bb -> distr_b_all bb >>= fun (bb,c) -> (return (Or bb, c))
  | And bb -> distr_b_all bb >>= fun (bb,c) -> (return (And bb, c))
  | Implies (b1,b2) -> 
   project distr_b (b1,b2) >>= fun ((b1',c1),(b2',c2)) ->
   return (Implies(b1',b2'), c1 @ c2)
  | Iff bb -> distr_b_all bb >>= fun (bb,c) -> (return (Iff bb, c))
  | Eq (a1,a2) -> 
   project distr_a (a1,a2) >>= fun ((a1',c1),(a2',c2)) -> 
   return (Eq(a1',a2'),c1 @ c2)
  | Ge (a1,a2) ->
   project distr_a (a1,a2) >>= fun ((a1',c1),(a2',c2)) -> 
   return (Ge(a1',a2'),c1 @ c2)
  | Gt (a1,a2) -> 
   project distr_a (a1,a2) >>= fun ((a1',c1),(a2',c2)) -> 
   return (Gt(a1',a2'),c1 @ c2)
  | b -> return (b,[])
 in M.get >>= fun c -> cachem c.distr_b_cache distr_b' b
and distr_b_all bb = 
 map distr_b bb >>= fun bb' ->
 return (List.foldl (fun (bb,cc) (b,c) -> (b::bb,c@cc)) ([],[]) bb')
;;

let norm_arithmetic = distr_b


(* -------------------------------------------------------------------------- *)
(* --- 3. resolve nonlinearity ---------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

(* repeatedly replace term of form x * y by fresh z, adding constraints 
   -2z + x + y >= 0, z - x - y >= -1 *)
let rec abstract =
 let replace x y = 
  let rep (x,y) = 
   fresha () >>= fun z ->
   let x,y = Vara x, Vara y in
   let m1,m2 = const (-1), const (-2) in
   let c1 = Ge (s_add [s_mul[m2; z]; x; y], Const Int64.zero) in
   let c2 = Ge (s_add [s_mul[m1; x]; s_mul[m1; y]; z], m1) in
   add_constraints [c1;c2] >> return (to_var z)
  in M.get >>= fun c -> cachem c.vmult rep (x,y) 
 in function
  | [x] -> return x
  | x :: xs -> abstract xs >>= fun y -> replace x y
  | [] -> failwith "empty var list in abstract"
;;

let collect aa =
 let (cs,vs) = List.partition is_const aa in
 let c = List.foldl Int64.mul Int64.one (List.map to_const cs) in
 if List.is_empty vs then return (Const c) 
 else
  abstract (List.map to_var vs) >>= fun v ->
  return (if c = Int64.one then Vara v else s_mul [Const c; Vara v])
;;

(* replace all Mul fs by linear terms, adding extra constraints *)
let linearize =
 let rec lin_a a =
  let lin_a' = function
   | Add aa -> map lin_a aa >>= (return <.> s_add)
   | Sub aa -> map lin_a aa >>= (return <.> mk_sub)
   | Mul aa -> collect aa
   | Ite (b,a1,a2) -> 
    project lin_a (a1, a2) >>= fun (a1',a2') ->
    lin_b b >>= fun b' ->
    return (Ite(b',a1',a2'))
   | a -> return a
  in M.get >>= fun c -> cachem c.linearize_a_cache lin_a' a
 and lin_b b =
  let lin_b' = function
   | Not b -> lin_b b >>= (return <.> mk_not)
   | Or bb -> map lin_b bb >>= (return <.> mk_or)
   | And bb -> map lin_b bb >>= (return <.> mk_and)
   | Implies (b1,b2) -> project lin_b (b1,b2) >>= (return <.> mk_imp)
   | Iff bb -> map lin_b bb >>= (return <.> mk_iff)
   | Eq (a1,a2) -> project lin_a (a1, a2) >>= (return <.> mk_eq)
   | Ge (a1,a2) -> project lin_a (a1, a2) >>= (return <.> mk_ge)
   | Gt (a1,a2) -> project lin_a (a1, a2) >>= (return <.> mk_gt)
   | b -> return b
  in M.get >>= fun c -> cachem c.linearize_b_cache lin_b' b
 in lin_b
;;

(* -------------------------------------------------------------------------- *)
(* --- 4. massage atoms to a_1 x_1 + .... + a_n x_n >= c -------------------- *)
(* -------------------------------------------------------------------------- *)

let rec neg = function
 | Add aa -> s_add (List.map neg aa)
 | Const c -> Const (Int64.neg c)
 | Vara x -> s_mul [const (-1); Vara x]
 | Mul [Const c; a] -> s_mul [Const (Int64.neg c); a]
 | _ -> failwith "negate: undesired pattern"
;;

let split = function
 | (Const _) as c -> (c,[])
 | (Vara _) as x -> (Const Int64.zero, [x])
 | Add aa -> let cs, xs = List.partition is_const aa in add cs, xs
 | (Mul _) as a -> (Const Int64.zero, [a])
 | _ -> failwith "split: undesired pattern"
;;

let rec massage' = function
 | Bot -> Bot
 | Top -> Top
 | Varb x -> Varb x
 | Not b -> Not (massage' b)
 | Or bs -> Or (List.map massage' bs)
 | And bs -> And  (List.map massage' bs)
 | Ge(ls,rs) ->
  let (cl, vl), (cr,vr) = split ls, split rs in
  let c = Const (Int64.sub (to_const cr) (to_const cl)) in
  Ge(s_add ((List.map neg vr) @ vl), c)
 | Gt(ls,rs) ->
  let (cl, vl), (cr,vr) = split ls, split rs in
  let c = Int64.sub (to_const cr) (to_const cl) in
  Ge(s_add ((List.map neg vr) @ vl), Const (Int64.succ c))
 | Eq (ls,rs) ->
  let (cl, vl), (cr,vr) = split ls, split rs in
  let c = Int64.sub (to_const cr) (to_const cl) in
  let a = s_add [neg (s_add vr); s_add vl] in
  let a' = s_add [neg (s_add vl); s_add vr] in
  And [Ge(a, Const c); Ge(a', Const (Int64.neg c))]
 | Implies (b1,b2) -> Implies (massage' b1, massage' b2)
 | Iff bs -> Iff (List.map massage' bs)
 | _ -> failwith "massage: undesired pattern"
;;


(* -------------------------------------------------------------------------- *)
(* --- 5. translate propositional structure to PB --------------------------- *)
(* -------------------------------------------------------------------------- *)

let replace_iff bs =
 if List.length bs < 2 then Top
 else
  let rec rem = function
   | b1 :: b2 :: bs -> And[Implies(b1,b2); rem (b2 :: bs)]
   | _ -> Top
  in let b,b' = List.hd bs, List.last bs in And[Implies(b',b); rem bs]
;;

(* push negations to atoms, replaces Iffs, Implies, Eqs and Gts *)
let rec nnf b =
 let nnf' = function
  | Bot -> Bot
  | Top -> Top
  | (Varb _) as b -> b
  | (Not (Varb _)) as b -> b
  | Not b -> nnf (negate b)
  | Or bs -> s_or  (List.map nnf bs)
  | And bs -> s_and (List.map nnf bs)
  | Implies (b1,b2) -> Or[nnf (negate b1); nnf b2]
  | Iff bs -> nnf (replace_iff (List.map nnf bs))
  | Ge (a1,a2) -> Ge (a1,a2)
  | _ -> failwith "Undesired pattern in nnf"
 in cache nnf_cache nnf' b
and negate b =
 let negate' = function
  | Bot -> Top
  | Top -> Bot
  | Varb x -> Not (Varb x)
  | Not b -> b
  | Or bs -> And (List.map negate bs)
  | And bs -> Or (List.map negate bs)
  | Implies (b1,b2) -> And[b1; negate b2]
  | Iff [b] -> Top
  | Iff bs -> negate (replace_iff bs)
  | Ge (a1, Const c) -> Ge(neg a1, Const (Int64.succ (Int64.neg c)))
  | _ -> failwith "Undesired pattern in negate"
 in cache negate_cache negate' b
;;

(* remove propositional variables *)
let replace_pvars f =
let rec replace_pvars = function
 | Bot -> And [Ge (Vara "x1",const 1); Ge (Mul[const (-1); Vara "x1"], const 0)]
 | Top -> Top
 | Varb x -> Ge (Vara x, Const Int64.one)
 | Not (Varb x) -> Ge (Mul[const (-1); Vara x], const 0)
 | And bs -> And (List.map replace_pvars bs)
 | Or bs -> Or (List.map replace_pvars bs)
 | Ge (a1,a2) -> Ge (a1,a2)
 | _ -> failwith "undesired input in remove_bvars"
 in replace_pvars f
;;


(* assumes that constraint c has shape a_1x_1 + ... + a_kx_k >= b,
   and returns mv + ... + a_kx_k >= b such that if v=1 the
   constraint is satisfied *)
let add_conditional c v =
 let rec minval = function
  | Const a -> Int64.to_int a
  | Vara a -> 0
  | Add aa -> List.foldl (fun m x -> m + (minval x)) 0 aa
  | Sub aa -> List.foldl (fun m x -> m - (maxval x)) 0 aa
  | Mul [Const c; Vara _] -> min 0 (Int64.to_int c)
  | _ -> failwith "minval: undesired pattern"
 and maxval = function
  | Const a -> Int64.to_int a
  | Vara a -> 1
  | Add aa -> List.foldl (fun m x -> m + (maxval x)) 0 aa
  | Sub aa -> List.foldl (fun m x -> m - (minval x)) 0 aa
  | Mul [Const c; Vara _] -> max 0 (Int64.to_int c)
  | _ -> failwith "maxval: undesired pattern"
 in
 match c with 
  | Ge(s, Const c) -> 
   let m = Int64.of_int (minval s - (Int64.to_int c)) in
   Ge(s_add [s;Mul [Const m; v]], const (minval s))
  | _ -> failwith "add_conditional: undesired pattern"
;;

let rec prop_to_pb vs = function
 | Top -> return ()
 | Or bs -> 
  freshs (List.length bs) >>= fun zs ->
  add_constraint (Ge(s_add zs, const 1)) >>
  iter (fun (d,z) -> prop_to_pb (z::vs) d) (List.zip bs zs)
 | And bs -> iter (prop_to_pb vs) bs
 | Ge (a1,a2) -> add_constraint (List.foldl add_conditional (Ge (a1,a2)) vs) 
 | _ -> failwith "undesired input in prop_to_pb"
;;

let transform_skeleton = prop_to_pb [] <.> replace_pvars <.> nnf


(* -------------------------------------------------------------------------- *)
(* --- overall translation -------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
let translate f fs =
 (*F.printf "translate %a\n%!" S.fprintf_b f;*)
 replace_vars f >>= fun f ->
 (*F.printf "after replace_vars: %a\n%!" S.fprintf_b f;*)
 norm_arithmetic f >>= fun (f,cs) -> 
 let f = And (f::cs) in
 (*F.printf "after normalization:\n %a\n%!" S.fprintf_b f;*)
 linearize f >>= fun f ->
 (*M.get >>= fun c -> let cs = c.pb_cs in
 F.printf "after linearization: %a\n%!" S.fprintf_b f;
 F.printf "constraints:";
 List.iter (fun c -> F.printf " %a\n%!" S.fprintf_b c) cs;*)
 let f = massage' f in
 (*F.printf "after massage: %a\n%!" S.fprintf_b f;*)
 transform_skeleton f  >>
 M.get >>= fun c -> let cs = c.pb_cs in
 (*F.printf "after skeleton transformation:";
 List.iter (fun c -> F.printf " %a\n%!" S.fprintf_b c) cs;*)
 return cs
;;

let solve_cnf cs =
  M.get >>= fun c ->
  let to_var v = lift (Logic.cache_bool c.cnf_vars v) in
  let to_lit (v, s) = to_var v >>= fun x -> 
   return (if s then x else Logic.neg x) in
 let to_clause = (liftM Logic.big_or) <.> (map to_lit) in
 map to_clause cs >>= fun cs' -> 
 let phi = Logic.big_and cs' in
(* Format.printf "CNF: %a\n%!" L.fprintf_p phi;*)
 lift (Logic.solve phi)
;;

let reconstruct ass = 
(* Format.printf "CNF assignment: %a\n%!" L.fprintf_assignment ass;*)
 let rec eval_a ass = function
  | Const a -> N.of_64_int a
  | Vara x -> (try if H.find ass x then N.one else N.zero
   (* values of some variables do not matter *)
   with Not_found -> 
   Debug.debug (F.sprintf "eval_a: unassigned %s\n%!" x); 
   N.zero)
  | Add aa -> List.foldl1 N.add (List.map (eval_a ass) aa)
  | Mul aa -> List.foldl1 N.mul (List.map (eval_a ass) aa)
  | _ -> failwith "unexpected pattern in eval_a"
 in 
 M.get >>= fun c ->
 let e = H.create 100 in
 let add_a k v h = lift (L.eval_p v ass) >>= fun v' -> H.add h ((*var_prefix ^*) k) v'; return h in
 h_foldm add_a c.cnf_vars e >>= fun ass' ->
(* H.iter (fun k v -> Format.printf "%s:%i\n" k (if v then 1 else 0)) ass';*)
 let a_a = H.fold (fun v a r -> (v,eval_a ass' a) :: r) c.avar_tbl [] in
 let a_p = H.fold (fun v v' r -> (v, try H.find ass' v' with Not_found -> failwith "not found in eval_b") :: r) c.bvar_tbl [] in
 return (a_a, a_p)
;;

let reconstruct_from_pb ass' =
 M.get >>= fun c ->
 let to_logic x = H.find c.logic_avar x in
 let rec eval_a = function
  | Const a -> return (N.of_64_int a)
  | Vara x -> (try lift (L.eval_a (to_logic x) ass') with 
   Not_found -> return N.zero)
   (* values of some variables do not matter *)
  | Add aa -> map eval_a aa >>= fun aa' -> return (List.foldl1 N.add aa')
  | Mul aa -> map eval_a aa >>= fun aa' -> return (List.foldl1 N.mul aa')
  | _ -> failwith "unexpected pattern in eval_a"
 in
 let at = H.fold (fun v a r -> (v,a) :: r) c.avar_tbl [] in
 map (fun (v, a) -> eval_a a >>= fun a' -> return (v,a')) at >>= fun a_a ->
 let pt = H.fold (fun v p r -> (v,p) :: r) c.bvar_tbl [] in
 map (fun (v, a) -> eval_a (Vara a) >>= fun a' -> return (v,a' = N.one)) pt >>= fun a_p ->
 return (a_a, a_p)
;;

(*TODO: unify reconstruction functions*)
let reconstruct2 ass = 
 M.get >>= fun c -> 
 let rec eval_a = function
  | Const a -> return (N.of_64_int a)
  | Vara x -> (try (return (List.assoc x (fst ass))) with Not_found -> return N.zero)
   (* values of some variables do not matter *)
  | Add aa -> map eval_a aa >>= fun aa' -> return (List.foldl1 N.add aa')
  | Mul aa -> map eval_a aa >>= fun aa' -> return (List.foldl1 N.mul aa')
  | _ -> failwith "unexpected pattern in eval_a"
 in
 let at = H.fold (fun v a r -> (v,a) :: r) c.avar_tbl [] in
 map (fun (v, a) -> eval_a a >>= fun a' -> return (v,a')) at >>= fun a_a ->
 let pt = H.fold (fun v p r -> (v,p) :: r) c.bvar_tbl [] in
 map (fun (v, a) -> eval_a (Vara a) >>= fun a' -> return (v,a' = N.one)) pt >>= fun a_p ->
 return (a_a, a_p)


let type_change cs =
 M.get >>= fun c ->
 let t' cs =
  let return = L.Monad.return in 
  let var v = L.cache_arith c.logic_avar (L.nat 1) v in
  let (>>=) = L.Monad.(>>=) in
  let rec ta = function
   | Vara v -> var v
   | Const c -> return (L.constant (N.of_64_int c))
   | Mul [Const c; Vara v]
   | Mul [Vara v; Const c] -> var v >>= fun x ->
    return (L.scale (N.of_64_int c) x)
   | Add al ->  L.Monad.map ta al >>= (return <.> L.big_sum)
   | _ -> failwith "Undesired pattern in ta"
  in 
  let tb = function
   | Ge (a, Const c) -> 
    ta a >>= fun a' -> return (a' <>=> (L.constant (N.of_64_int c)))
   | _ -> failwith "Undesired pattern in tb"
  in
  L.Monad.map tb cs >>= fun cs -> return (Logic.big_and cs)
 in lift (t' cs)
;;

let explode s =
 let rec ex i =
  if i >= String.length s then []
  else 
   let j = try String.index_from s i ' ' with Not_found -> String.length s in
   let x = String.sub s i (j-i) in
   if x = "" then ex (j+1) else x :: (ex (j+1))
 in ex 0
;;

let solve ib db ob solver opt ipt =
 let c = mk_ctx (if ib < 1 then 1 else ib) solver in
 (L.run ~dbits:db ~obits:ob (M.run c (
  let fs = ib, db, ob, ipt in
  let phi = And (ipt.assumptions@[ipt.formula]) in
  M.get >>= fun c -> 

  translate phi fs >>= fun cs -> 
  let _ = Debug.debug (Format.sprintf "translated:") in 
   (* let _ = F.printf "translated: %s@\n" (List.join S.b_to_string ";@\n" cs) in *)
  match solver with 
  | "" -> (*internal solver*)
    let _ = Debug.debug "using internal solver" in
    (M.lift (Pb2bdd.solve cs) >>= function
    | None -> return UNKNOWN
    | Some  ass -> 
    let _ = Debug.debug "internal solver done" in
    reconstruct2 ass >>= fun ass' -> return (S.SAT ass'))
  | "gpwi" -> (*gpw internal*)
  (let _ = Debug.debug (F.sprintf "using solver: %s" solver) in
  type_change cs >>= fun phi ->
  let t = Unix.gettimeofday () in
  lift (Logic.solve ~solver:(Logic.Gpw (explode opt)) phi) >>= function
   | None -> return UNKNOWN
   | Some ass -> 
    let t = Unix.gettimeofday () -. t in
    if !Debug.on then Format.printf " solving:     %f\n%!" t;
    reconstruct_from_pb ass >>= fun ass' -> 
       return (SAT ass'))
  | "minisatpi" -> (*minisat+ internal*)
  (let _ = Debug.debug (F.sprintf "using solver: %s" solver) in
  type_change cs >>= fun phi ->
  let t = Unix.gettimeofday () in
  lift (Logic.solve ~solver:(Logic.MiniSatP) phi) >>= function
   | None -> return UNKNOWN
   | Some ass -> 
    let t = Unix.gettimeofday () -. t in
    if !Debug.on then Format.printf " solving:     %f\n%!" t;
    reconstruct_from_pb ass >>= fun ass' -> 
       return (SAT ass'))
  | _ -> (*gpw external*)
   (let _ = Debug.debug (F.sprintf "using solver: %s" solver) in
   match Pb2cnf.translate cs (solver ^ " " ^ opt) with
    | None -> return UNKNOWN
    | Some cnf -> (
     solve_cnf cnf >>= function
      | None -> return UNKNOWN
      | Some ass -> 
       reconstruct ass >>= fun ass' -> 
       (*assert (check_ass ipt ass');
       if !Debug.on then F.printf "Assignment verified: %i\n%!" 
        (if check_ass ipt ass' then 1 else 0); *)
       return (SAT ass')))
 )))
;;
