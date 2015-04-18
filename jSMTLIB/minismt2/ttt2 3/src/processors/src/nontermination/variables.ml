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
module C = Context;;
module F = Format;;
module M = Monad;;
module P = Problem;;
module S = Substitution;;
module XO = XmlOutput;;

(*** TYPES ********************************************************************)
type flags = {help : bool ref};;
type t = P.t * Loop.t;;

(*** GLOBALS ******************************************************************)
let code = "var";;
let name = "Fresh Variable Processor";;
let keywords = ["variable condition";"nontermination"];;
let flags = {help = ref false};;

let comment =
 "Defines a processor which proves nontermination of a given TRS by checking \
  whether a left-hand side is a variable or a right-hand side introduces a \
  fresh variable. \
    For relative termination problems it is checked that there are no \
  left-erasing or right-duplicating rules in the relative component. \
  (This is a necessary condition for relative termination to be \
  found in Geser's PhD thesis.)"
;;

let spec =
 let spec = [
  ("--help",Arg.Set flags.help,"Prints information about flags.");
  ("-help",Arg.Set flags.help,"Prints information about flags.");
  ("-h",Arg.Set flags.help,"Prints information about flags.")]
 in
 Arg.alignx 80 spec
;;

let help = (comment,keywords,List.map Triple.drop_snd spec);;

(*** FUNCTIONS ****************************************************************)
let (>>=) = M.(>>=);;
let init _ = flags.help := false;;

(* Destructors *)
let get_loop = snd;;
let get_ip = fst;;

(*If possible, get some variable (together with it's position) of the rhs that
is not a variable of the lhs, otherwise return None.*)
let get_free_var_pos l r =
  let xs = Term.vars l in
  List.find_option (not <.> flip List.mem xs) (Term.vars r)
  |> Option.map (fun x -> (x, List.hd (Term.var_pos x r)))
;;

(*Check variable condition and provide counterexample if not satisfied.*)
let trivial_loop trs =
  Trs.find_option (not <.> Rule.is_rewrite_rule) trs
  |> Option.map Rule.to_terms
  |> Util.Monad.Option.(=<<) (function
    | (Term.Var x as l, r) -> Some (Loop.make [l] C.Hole (S.singleton x r))
    | (l, r) ->
      get_free_var_pos l r
      |> Option.map (fun (x, p) ->
        let s = S.singleton x l in
        Loop.make [l] (C.of_term p (S.apply_term s r)) s))
;;


(* Processor *)
let solve fs p =
  let configurate s = F.printf "%s@\n%!" s; flags.help := true in
  (try init (); Arg.parsex code spec fs with Arg.Bad s -> configurate s);
  if !(flags.help) then (Arg.usage spec ("Options for "^code^":"); exit 0);
  if P.is_sp p then
    M.return (Option.map (Pair.make p) (trivial_loop (P.get_trs p)))
  else if P.is_rp p then
    let (s, w) = P.get_sw p in
    (match trivial_loop s with
      | Some _ as loop -> M.return loop
      | None ->
      (*See page 18 (Necessary Condition) of Geser's thesis.*)
      (*PS: I want do-notation!*)
      Trs.find_option (not <.> List.is_empty <.> Term.vars <.> Rule.rhs) s
      |> Option.map Rule.to_terms
      |> Option.fold (fun (g, d) ->
        Trs.find_option Rule.is_right_erasing w
        |> Option.map Rule.to_terms
        |> function
          | Some (l, r) ->
            (* x : Var(r)\Var(l) *)
            (*this x needs to be disjoint from variables in g and d*)
            Elogic.renaming [l; r] >>= fun ren ->
            let l' = S.apply_term ren l in
            let r' = S.apply_term ren r in
            get_free_var_pos l' r'
            |> Option.map (fun (x, _) ->
              let y = List.hd (Term.vars d) in       
              let xg = S.singleton x g in
              let yl = S.singleton y l' in
              let xd = S.singleton x d in
              let rxd = S.apply_term xd r' in
              let q = List.hd (Term.var_pos y rxd) in
              let c = C.of_term q (S.apply_term xd r') in
              Loop.make [l'; S.apply_term yl (S.apply_term xg r')] c S.empty)
            |> M.return
          | None ->
            Trs.find_option (fun r -> Term.is_var (Rule.lhs r) && Rule.is_duplicating r) w
            |> Option.map Rule.to_terms
            |> Option.map (fun (Term.Var x, r) ->
              let p::q::_ = Term.var_pos x r in
              let r' = Term.replace p d r in
              let xg = S.singleton x g in
              let c = C.of_term q r' in
              Loop.make [g; S.apply_term xg r] c S.empty)
            |> M.return
      ) (M.return None)
    ) >>= fun loop ->
    M.return (Option.map (Pair.make p) loop)
  else M.return None
;;

(* Compare Functions *)
let equal p q = P.equal (get_ip p) (get_ip q);;

(* Printers *)
let fprintf fs fmt p =
 F.fprintf fmt "@[<1>%s:@ " name; Loop.fprintf fmt (get_loop p) >>= fun _ ->
 F.fprintf fmt "@\n"; List.hd fs fmt >>= fun _ -> M.return (F.fprintf fmt "@]")
;;

let fprintfx _ (p, loop) = Loop.fprintfx loop p;;
