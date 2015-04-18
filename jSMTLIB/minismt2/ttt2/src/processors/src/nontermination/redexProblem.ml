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

(*** MODULES ******************************************************************)
module Pos = Position;;
module Subst = Substitution;;

type loop = Rule.t * (Rule.t * Pos.t) list

let apply_var mu x = Subst.apply x (Term.Var x) mu;;

(*All variables that can occur in a term of the form 't\mu^n' for
arbitrary 'n'.*)
let allvars mu t = fix
  ~eq:List.equal
  (List.flat_map (Term.vars <.> apply_var mu))
  (Term.vars t)
;;

(*Subterms that have to be considered to cover all potential matchings.*)
let subterms_to_consider ws mu t =
  Term.subterms ~p:Term.is_fun t @
  List.flat_map
    (Term.subterms ~p:Term.is_fun <.> apply_var mu)
    ws
;;

let vincr mu =
  (*compute 1-step non-increasing and increasing variables*)
  let (ninc, inc) = Subst.fold (fun x t (ninc, inc) -> match t with
    | Term.Var y -> ((x, y) :: ninc, inc)
    | _          -> (ninc, x :: inc)
  ) mu ([], [])
  in
  fix
    ~eq:List.equal
    (fun vs -> List.foldl (fun vs (x, y) ->
      if List.mem y vs
        then x :: vs
        else vs) vs ninc)
    inc
;;

(*Initial Matching Problems*)
let initial_mps ws mu = function
  | (t, (Term.Var _ as l)) ->  [(t, l)]
  | (t, l) -> List.map (fun u -> (u, l)) (subterms_to_consider ws mu t)
;;

(*Simplify matching problem into solved form.*)
let simp_mp mu mp =
  let vs = vincr mu in
  let rec simp_mp' vs mp s = match mp with
    | [] -> Some (s, 0)
    | ((t, Term.Var x)::mp) -> simp_mp' vs mp ((t, x) :: s)
    | ((Term.Fun(f, ss), Term.Fun(g, ts))::mp) ->
      if Function.equal f g && List.length ss = List.length ts
        then simp_mp' vs (List.zip ss ts @ mp) s
        else None
    | ((Term.Var x, Term.Fun(g, ts)) as tl ::mp) ->
      if List.mem x vs
        then (
          let mapmu = List.map (fun (t, l) -> (Subst.apply_term mu t, l)) in
          let mapmu' = List.map (fun (t, l) -> (Subst.apply_term mu t, l)) in
          match simp_mp' vs (mapmu (tl :: mp)) (mapmu' s) with
            | Some (mp', i) -> Some (mp', i+1)
            | None -> None
        ) else None
  in
  simp_mp' vs mp []
;;

(*Initial Identity Problems*)
let rec initial_ips = function
  | [] -> []
  | (t, l) :: smps ->
    List.map (Pair.make t <.> fst) (List.filter ((=) l <.> snd) smps)
      @ initial_ips smps
;;

let rec conflicts mu = function
  | (s, Term.Var y, n) when n > 0 -> conflicts mu (s, apply_var mu y, n-1)
  | ((Term.Var _ as x), (Term.Var _ as y), 0) -> if x = y then [] else [(x, y, 0)]
  | ((Term.Fun(_, _) as s), (Term.Var _ as y), 0) -> [(y, s, 0)]
  | ((Term.Var _ as x), (Term.Fun(_, _) as t), n) -> [(x, t, n)]
  | ((Term.Fun(f, ss) as s), (Term.Fun(g, ts) as t), n) ->
    if Function.equal f g && List.length ss = List.length ts
      then List.flat_map (fun (si, ti) -> conflicts mu (si, ti, n)) (List.zip ss ts)
      else [(s, t, n)]
;;

let ident_solve mu (s, t) =
  let rec ident_solve' mu ss ip =
    let cs = conflicts mu ip in
    if List.exists (Term.is_fun <.> Triple.fst) cs
      || List.exists (fun (u, v, _) -> List.exists (fun (u', v', _) -> u = u' && v = v') ss) cs
      then None
      else (
        match Util.Monad.Option.map
          (fun (u, v, m) -> ident_solve' mu ((u, v, m) :: ss) (Subst.apply_term mu u, v, m+1))
          cs
        with
          | Some ns -> Some (List.foldl1 (max) ns + 1)
          | None -> None
      )
  in
  ident_solve' mu [] (s, t, 0)
;;

let mp_to_id mu tl =
  match simp_mp mu [tl] with
    | None -> None
    | Some (smps, i) ->
      let rs = List.map (ident_solve mu) (initial_ips smps) in
      if List.exists (Option.is_none) rs
        then None
        else Some (List.foldl1 (max) (List.map (Option.the) rs) + i)
;;

let solvable mu (t, l) =
  let ws = allvars mu t in
  let mps = initial_mps ws mu (t, l) in
  let sols = List.map (mp_to_id mu) mps in
  List.exists (Option.is_some) sols
;;
