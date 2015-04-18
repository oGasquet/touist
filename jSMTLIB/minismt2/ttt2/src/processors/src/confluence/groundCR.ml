(* Copyright 2011 Bertram Felgenhauer
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
module F = Format;;
module M = Monad;;
module P = Problem;;
module XO = XmlOutput;;

module H = Hashtbl;;

type eqn = (int * int * int) list;;
type rel = bool array array;;

(*** TYPES ********************************************************************)
type flags = {
  help: bool ref;
};;

type t = {
  ip : P.t;
  result : Result.t;
};;

(*** CONSTRUCTORS *************************************************************)
let make p r = {
  ip = p;
  result = r;
};;

(*** DESTRUCTORS **************************************************************)
let get_ip t = t.ip;;
let get_result t = t.result;;

(*** GLOBALS ******************************************************************)
let code = "groundcr";;
let name = "Ground Confluence Processor";;
let keywords = ["confluence";"nonconfluence"];;

let flags = {
  help = ref false;
};;

let init _ =
 flags.help := false;
;;

let comment =
 "Decides whether the given applicative, ground TRS is confluent."
;;

let spec =
 let spec = [
  ("--help",Arg.Set flags.help,"Prints information about flags.");
  ("-help",Arg.Set flags.help,"Prints information about flags.");
 ] in
 Arg.alignx 80 spec
;;

let help = (comment,keywords,List.map Triple.drop_snd spec);;

(*** FUNCTIONS ****************************************************************)
let (>>=) = M.(>>=);;

(* Flatten a TRS R0.
 * Result is (eq, n, rs).
 * Subterms of the original TRS are mapped to integers 0 to n-1.
 * The flattened TRS has an equational part eq and a rewriting part rs.
 * eq is a list of triples (u, v, w) representing rules (u o v) -> w.
 * rs is a list of pairs (u, v), each representing a rewrite rule u -> v.
 *
 * eq describes a mapping of subterms of R0 to its subterms; there is
 * a unique constant from 0 to n-1 representing each subterm of R0.
 *)
let flatten : Trs.t -> (int * eqn * (int * int) list) =
fun trs ->
  let
    (* custom state monad *)
    (>>=) f g = fun s -> let (s', r) = f s in g r s'
  in let
    (* assign numbers to function symbols, reusing previous assignments *)
    mkcon f (cons, apps, i) =
      try ((cons, apps, i), H.find_ f cons)
      with Not_found -> ((H.add_ f i cons, apps, i+1), i)
  in let
    (* assign numbers to applications of the 'apply' operator *)
    mkapp a b (cons, apps, i) =
      try let apps_a = H.find_ a apps in
        try let n = H.find_ b apps_a in
          ((cons, apps, i), n)
        with Not_found ->
          ((cons, H.replace_ a (H.add_ b i apps_a) apps, i+1), i)
      with Not_found ->
        ((cons, H.add_ a (H.singleton b i) apps, i+1), i)
  in let rec
    term = function
    | Term.Fun (f, []) -> mkcon f
    | Term.Fun (_, [a; b]) ->
      term a >>= fun a' ->
      term b >>= fun b' ->
      mkapp a' b'
    | _ -> failwith "Impossible."
  in let
    rule rule (s, rs) =
      (term (Rule.lhs rule) >>= fun l ->
      term (Rule.rhs rule) >>= fun r ->
      fun s -> (s, (l, r) :: rs)) s
  in let
    ((_, apps, n), rs) =
      Trs.fold rule ((H.create 0, H.create 0, 0), []) trs
  in let
    eq = H.fold (fun u -> H.fold (fun v w eq -> (u, v, w) :: eq)) apps []
  in
  (* F.printf "G: %d / %d / %d\n" (H.size apps) (List.length rs) n; *)
  (* List.iter (fun (u, v, w) -> F.printf "  %d o %d -> %d\n" u v w) eq; *)
  (* List.iter (fun (u, v) -> F.printf "  %d -> %d\n" u v) rs; *)
  (n, eq, rs)
;;

(* Rewrite closure of a flattened TRS, ala Plaisted:
 *
 * We have u --> v in the result whenever u -->^* v in the original TRS.
 *
 * The result is a relation between the constants created by the flattening
 * step, i.e., between the subterms of the original TRS.
 *)
let rewrite_closure : (int * eqn * (int * int) list) -> rel =
fun (n, eq, rs) ->
  let
    (* rc will be the result *) 
    rc = Array.make_matrix n n false and
    (* l stores eq rules u o v -> w, indexed by u; r stores them indexed by v *)
    l = Array.make n [] and r = Array.make n []
  in let
    eqn (u, v, w) =
      l.(u) <- (v, w) :: l.(u);
      r.(v) <- (u, w) :: r.(v);
  in let rec
    (* add a rule u -> v *)
    add (u, v) =
      if not rc.(u).(v) then (
        rc.(u).(v) <- true;
        (* transitivity *)
        for w = 0 to n-1 do
          if rc.(w).(u) then add (w, v); (* w -> u -> v *)
          if rc.(v).(w) then add (u, w); (* u -> v -> w *)
        done;
        (* left monotonicity *)
        List.iter (fun (u1, u2) ->
          List.iter (fun (v1, v2) ->
            if rc.(u1).(v1) then add (u2, v2); (* u2 = u o u1 -> v o v1 = v2 *)
          ) l.(v);
        ) l.(u);
        (* right monotonicity *)
        List.iter (fun (u1, u2) ->
          List.iter (fun (v1, v2) ->
            if rc.(u1).(v1) then add (u2, v2); (* u2 = u1 o u -> v1 o v = v2 *)
          ) r.(v);
        ) r.(u);
      );
  in
  (* fill l and r *)
  List.iter eqn eq;
  (* ensure reflexivity *)
  for i = 0 to n-1 do add (i, i); done;
  (* process rules one by one *)
  List.iter add rs;
  (* for i = 0 to n-1 do for j = 0 to n-1 do
    if rc.(i).(j) then F.printf "* %d -> %d\n" i j; done; done; *)
  rc
;;

(* Congruence closure, the rewrite closure of R and its inverse.
 *
 * We have u --> v in the result whenever u <-->^* v in the original TRS.
 *)
let congruence_closure : (int * eqn * (int * int) list) -> rel =
fun (n, eq, rs) ->
  rewrite_closure (n, eq, rs @ List.map (fun (a, b) -> (b, a)) rs)
;;

(* Calculate top stabilizable sides.
 *
 * A side u o v or constant u is top-stabilizable if it can be rewritten to
 * an (rc + eq)-normal form that is not a constant in a sequence of
 * (cc + eq^-1)-steps.
 *)
let topstabilizable :
  (int * eqn * (int * int) list) -> rel -> rel -> rel =
fun (n, eq, _) rc cc ->
  let
    (* nf stores (rc + eq)-normal forms of the form u o v *)
    nf = Array.make_matrix n n true and
    (* res.(u).(v) is [w] if u o v -> w in eq *)
    res = Array.make_matrix n n [] and
    (* cls.(u) stores the cc-equivalence-class belonging to u *)
    cls = Array.make n [] and
    (* sides collects top-stabilizable sides *)
    sides = Array.make_matrix n n false and
    (* consts collects top-stabilizable constants *)
    consts = Array.make n false
  in let
    (* mark terms reducible by eq/rc. assumes that rc is transitive. *)
    eqn (u, v, w) =
      for u' = 0 to n-1 do
        if rc.(u').(u) then
          for v' = 0 to n-1 do
            if rc.(v').(v) then
              (* u' o v' ->_rc u o v' ->_rc u o v ->_eq w *)
              nf.(u').(v') <- false;
          done;
      done;
      res.(u).(v) <- w :: res.(u).(v);
  in let rec
    (* add top-stabilizable u o v to 'sides' *)
    add_side u v =
      if not sides.(u).(v) then (
        let cs = ref [] in
        List.iter (fun u' ->
          List.iter (fun v' ->
            (* any cc-equivalent side is also top-stabilizable *)
            sides.(u').(v') <- true;
            (* any eq/cc-predecessor of u o v is a top-stabilizable constant *)
            cs := res.(u').(v') @ !cs;
          ) cls.(v)
        ) cls.(u);
        List.iter add_const !cs;
      );
  and
    (* add top-stabilizable u to 'consts' *)
    add_const u =
      if not consts.(u) then (
        consts.(u) <- true;
        for v = 0 to n-1 do
          (* u o v is top-stabilizable if either u or v is *)
          add_side u v;
          add_side v u;
        done;
      );
  in
  (* fill nf *)
  List.iter eqn eq;
  (* for u = 0 to n-1 do for v = 0 to n-1 do
    if nf.(u).(v) then F.printf "NF %d o %d\n" u v; done; done; *)
  (* fill cls *)
  for u = 0 to n-1 do
    for v = 0 to n-1 do
      if cc.(u).(v) then cls.(u) <- v :: cls.(u);
    done;
  done;
  (* fill sides and consts *)
  for u = 0 to n-1 do
    for v = 0 to n-1 do
      if nf.(u).(v) then add_side u v;
    done;
  done;
  (* for u = 0 to n-1 do if consts.(u) then F.printf "TS %d\n" u; done; *)
  (* for u = 0 to n-1 do for v = 0 to n-1 do
    if sides.(u).(v) then F.printf "TS %d o %d\n" u v; done; done; *)
  sides
;;

(* Joinability for (eq^- + rc).
 *
 * Note that the code is very similar to the rewrite closure, with
 * a couple of significant differences:
 *
 * - rc is constant
 * - the direction of one transitivity check is different.
 *)
let joinable : (int * eqn * (int * int) list) -> rel -> rel -> rel =
fun (n, eq, _) rc cc ->
  let
    (* join will be the result *) 
    join = Array.make_matrix n n false and
    (* l stores eq rules u o v -> w, indexed by u; r stores them indexed by v *)
    l = Array.make n [] and r = Array.make n []
  in let
    eqn (u, v, w) =
      l.(u) <- (v, w) :: l.(u);
      r.(v) <- (u, w) :: r.(v);
  in let rec
    (* add eq/rc-joinable pair (u, v) *)
    add u v =
      if not join.(u).(v) then (
        join.(u).(v) <- true;
        join.(v).(u) <- true;
        (* transitivity *)
        for w = 0 to n-1 do
          if rc.(w).(u) then add w v; (* w -> u -> ? <- v *)
          if rc.(w).(v) then add u w; (* u -> ? <- v <- w *)
        done;
        (* left monotonicity *)
        List.iter (fun (u1, u2) ->
          List.iter (fun (v1, v2) ->
            if join.(u1).(v1) then add u2 v2;
              (* u2 = u o u1 -> ? <- v o v1 = v2 *)
          ) l.(v);
        ) l.(u);
        (* right monotonicity *)
        List.iter (fun (u1, u2) ->
          List.iter (fun (v1, v2) ->
            if join.(u1).(v1) then add u2 v2;
              (* u2 = u1 o u -> ? <- v1 o v = v2 *)
          ) r.(v);
        ) r.(u);
      );
  in
  (* fill l and r *)
  List.iter eqn eq;
  (* ensure reflexivity *)
  for u = 0 to n-1 do add u u; done;
  (* for u = 0 to n-1 do; for v = 0 to n-1 do
    if join.(u).(v) then F.printf "| %d %d\n" u v; done; done; *)
  join
;;

(* Finally, the confluence check.
 *)
let is_confluent :
  (int * eqn * (int * int) list) -> rel -> rel -> rel -> bool =
fun (n, eq, rs) rc cc tops ->
  let
    (* representatives for the cc equivalence classes *)
    repr = Array.make n (-1) and
    (* top-stabilizable eq left-hand sides, by representative of rhs *)
    eq_repr = Array.make n [] and
    (* see 'joinable' *)
    join = joinable (n, eq, rs) rc cc
  in
  (* fill in repr *)
  for u = 0 to n-1 do
    if repr.(u) < 0 then
      for v = u to n-1 do
        if cc.(u).(v) then
          repr.(v) <- u;
      done;
  done;
  (* fill in eq_repr *)
  List.iter (fun (u, v, w) ->
    if tops.(u).(v) then
      eq_repr.(repr.(w)) <- (u, v) :: eq_repr.(repr.(w));
  ) eq;
  try
    (* fun / fun condition:
     * All equivalent top-stabilizable sides have equivalent arguments.
     *)
    for w = 0 to n-1 do
      if not (List.is_empty eq_repr.(w)) then
        let (u, v) = List.hd eq_repr.(w) in
        List.iter (fun (u', v') ->
          if not cc.(u).(u') || not cc.(v).(v') then
            raise Exit;
        ) (List.tl eq_repr.(w));
    done;
    (* fun / con condition:
     * Every constant equivalent to a top-stabilizable side can be
     * rewritten to a side with equivalent arguments by eq^- + rc.
     *)
    for w0 = 0 to n-1 do
      List.iter (fun (u, v) ->
        for w = 0 to n-1 do
          if cc.(w0).(w) then
            if not (List.exists (fun (u', v', w') ->
              cc.(u).(u') && cc.(v).(v') && rc.(w).(w')) eq)
            then raise Exit;
        done;
      ) eq_repr.(w0);
    done;
    (* con / con condition:
     * all equivalent constants are joinable.
     *)
    for u = 0 to n-1 do
      for v = 0 to n-1 do
        if cc.(u).(v) && not join.(u).(v) then
          raise Exit;
      done;
    done;
    true
  with
    Exit -> false
;;

(* Unlike Trs.is_applicative, we also accept TRSs with constants only.
 *)
let is_applicative r =
  let rec check_sig b = function
   | [] -> M.return true
   | f::fs ->
    M.find_ari f >>= fun a ->
    if a = 0 then check_sig b fs
    else if a = 2 && not b then check_sig true fs else M.return false
  in
  check_sig false (Trs.funs r)
;;

let groundcr p =
  let trs = P.get_trs p in
  is_applicative trs >>= fun c ->
  (* F.printf "%s\n" (if c then "APPL-YES" else "APPL-NO"); *)
  if not c || not (Trs.is_ground trs) then M.return None else
  let flat = flatten trs in
  let rc = rewrite_closure flat in
  let cc = congruence_closure flat in
  let tops = topstabilizable flat rc cc in
  let r = is_confluent flat rc cc tops in
  M.return (Some (if r then Result.make_yes [] else Result.make_no))
;;

let solve fs p =
 let configure s = F.printf "%s@\n%!" s; flags.help := true in
 (try init (); Arg.parsex code spec fs with Arg.Bad s -> configure s);
 if !(flags.help) then (Arg.usage spec ("Options for "^code^":"); exit 0);
 if P.is_crp p then
  groundcr p >>= fun r ->
  M.return (Option.map (make p) r)
 else
  M.return None
;;

(* Compare Functions *)
let equal p q = P.equal (get_ip p) (get_ip q);;

(* Printers *)
let fprintf fs fmt p = if Result.is_yes (get_result p)
  then M.return (F.fprintf fmt "@[<1>%s:@\nconfluent by decision procedure.@]" name)
  else M.return (F.fprintf fmt "@[<1>%s:@\nnon-confluent by decision procedure.@]" name)
;;

let fprintfx fs p = if Result.is_yes (get_result p)
  then XO.node "crProof" [XO.node "groundCR" []]
  else XO.node "crDisproof" [XO.node "groundCR" []]
;;
