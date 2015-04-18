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

(*** MODULES ******************************************************************)
module F = Format;;
module M = Monad;;
module O = Util.Option;;
module Pos = Position;;

(*** OPENS ********************************************************************)
open Prelude;;
open Util;;

(*** MODULES ******************************************************************)
module Make (L : LABEL) = struct
 (*** MODULES *****************************************************************)
 module E = Elogic.Make (L);;
 module M = M.Make (L);;
 module Parser = Parser.Make (L);;
 module Xml = Parser.Xml;;
 module S = Signature.Make (L);;
 module Sub = Substitution.Make (L);;
 module Term = Term.Make (L);;

 (*** TYPES *******************************************************************)
 type 'a m = 'a M.t;;
 type 'a p = 'a Parser.t;;
 type 'a x = 'a Xml.t;;
 type substitution = Sub.t;;
 type term = Term.t = Var of Variable.t | Fun of Function.t * term list;;
 type t = Term.t * Term.t;;
 
 (*** FUNCTIONS ***************************************************************)
 (* Parsers *)
 let (<?>) = Parser.(<?>);;
 let (>>=) = Parser.(>>=);;
 let (>>) = Parser.(>>);;

 let parse vars =
  Term.parse vars <?> "left-hand side" >>= fun lhs ->
  Parser.lex (Parser.string "->") <?> "arrow '->'" >>
  Term.parse vars <?> "right-hand side" >>= fun rhs ->
  Parser.return (lhs,rhs)
 ;;
 
 let of_string vars input =
  M.(>>=) M.get (fun s ->
   let m t = Parser.get_state >>= (Parser.return <.> Pair.make t) in
   let m = parse vars >>= m in
   match Parser.run m s (Parsec.StringInput.of_string input) with
    | Left e -> M.fail (Parsec.Error.to_string e)
    | Right(t,s) -> M.(>>) (M.set s) (M.return t))
 ;;
 
 (* xml transformer *)
 let (>>=) = Xml.(>>=);;
 let (>>) = Xml.(>>);;
 let (<?>) = Xml.(<?>);;
 let (<?) = Xml.(<?);;

 let xml = "rule" <?> Xml.node(
   "lhs" <?> Xml.node Term.xml >>= fun l ->
   "rhs" <?> Xml.node Term.xml >>= fun r ->
   Xml.return(l,r)
 ) <? "failed to transform rule";;

 let of_xml_string input =
   M.(>>=) M.get (fun s ->
   let module XP = Parsec.Xml.MakeParser(Parsec.StringParser) in
   match XP.parse (Parsec.StringInput.of_string input) with
     | Left e     -> M.fail(Parsec.Error.to_string e)
     | Right(_,x) ->
       let m t = Xml.get_state >>= (Xml.return <.> Pair.make t) in
       let m = xml >>= m in
       match Xml.run m s x with
         | Left e -> M.fail e
         | Right(t,s) -> M.(>>) (M.set s) (M.return t)
 );;
 
 let (<?>) = Util.(<?>);;
 let (>>=) = M.(>>=);;
 let (>>) = M.(>>);;
 
 (* Iterators *)
 let apply = Pair.apply;;
 let fold f = Pair.fold f f;;
 let count_fun f = fold ((+) <.> Term.count_fun f) 0
 let map = Pair.map;;
 let project = Pair.map;;
 let uncurry = Pair.uncurry;;
 
 (* Scan Functions *)
 let for_all f = Pair.for_all f f;;
 let exists f = Pair.exists f f;;
 
 (* Constructors and Destructors *)
 let invert = Pair.flip;;
 let lhs = fst;;
 let of_terms = Pair.make;;
 let reflect = map Term.reflect;;
 let reverse = map Term.reverse <?> "term is not a string";;
 let rhs = snd;;
 let to_terms = id;;
 
 (* Monadic Constructors and Destructors *)
 let rename r =
  E.renaming [lhs r;rhs r] >>= (M.return <.> flip map r <.> Sub.apply_term)
 ;;
 
 (* Compare Functions *)
 let compare = compare;;
 let equal r r' = compare r r' = 0;;
 
 (* Rule Symbols *)
 let symbols f = uncurry List.union <.> map f;;
 let cons = symbols Term.cons;;
 let funs = symbols Term.funs;;
 let vars = symbols Term.vars;;
 let symbols = symbols Term.symbols;;
 let left_cons r = Term.cons (lhs r);;
 let left_funs r = Term.funs (lhs r);;
 let left_vars r = Term.vars (lhs r);;
 let left_symbols r = Term.symbols (lhs r);;
 let right_cons r = Term.cons (rhs r);;
 let right_funs r = Term.funs (rhs r);;
 let right_vars r = Term.vars (rhs r);;
 let right_symbols r = Term.symbols (rhs r);;
 
 let left_root r =
  (O.the <.> Term.root <.> lhs <?> "left-hand side is a variable") r
 ;;
 
 let right_root r =
  (O.the <.> Term.root <.> rhs <?> "right-hand side is a variable") r
 ;;
 
 let roots r =
  let root g = try [O.the (Term.root (g r))] with Failure _ -> [] in
  let f = root lhs and g = root rhs in if f = g then f else List.rev_append f g
 ;;
 
 (* Rewriting *)
 let rewrite t p r = 
  let s = E.match_term (Term.subterm p t) (lhs r) in
  Term.replace p (Sub.apply_term s (rhs r)) t
 ;;

 let rewrites s p r t = 
 (*  rewrite s p r = t with E.Not_matchable -> false *)
 let l = Term.subterm p s in
  try
   let _ = E.match_problem [(l,lhs r);(Term.subterm p t,rhs r)] in
   Term.replace p l t = s
  with E.Not_matchable -> false
   | Failure _ -> false
 ;; 

 let reducts t r = 
  let f rs p = try (rewrite t p r :: rs) with E.Not_matchable -> rs in
  (List.foldl f [] <.> flip Term.fun_pos t <.> O.the <.> Term.root <.> lhs <?>
   "left-hand side is a variable") r
 ;;
 
 let redex_pos t r =
  let f p = E.matches (Term.subterm p t) (lhs r) in
  (List.filter f <.> flip Term.fun_pos t <.> O.the <.> Term.root <.> lhs <?>
   "left-hand side is a variable") r
 ;;
 
 (* Properties *)
 let is_build = for_all <.> Term.is_build;;
 let is_collapsing r = Term.is_var (rhs r);;
 let is_dummy = for_all Term.is_dummy;;
 
 let is_duplicating r =
  let rec count c x = function
   | Var y -> if x = y then c + 1 else c
   | Fun (_,ts) -> List.foldl (flip count x) c ts
  in
  let (l,r) = to_terms r in
  List.exists (fun x -> count 0 x l < count 0 x r) (Term.vars r)
 ;;
  
 let is_proper_embedded r =
  List.exists (Term.is_embedded (rhs r)) (Term.subterms (lhs r))
 ;;

 let is_embedded = uncurry (flip Term.is_embedded);;
 let is_flat = for_all Term.is_flat;;
 let is_ground = for_all Term.is_ground;;
 let is_linear = for_all Term.is_linear;;
 let is_shallow = for_all Term.is_shallow;;
 let is_string = for_all Term.is_string;;
 let is_size_preserving r = Term.size (lhs r) >= Term.size (rhs r);;
 let is_left_build fs = Term.is_build fs <.> lhs;;
 let is_left_dummy r = Term.is_dummy (lhs r);;
 let is_left_flat r = Term.is_flat (lhs r);;
 let is_left_ground r = Term.is_ground (lhs r);;
 let is_left_linear r = Term.is_linear (lhs r);;
 let is_left_shallow r = Term.is_shallow (lhs r);;
 let is_left_string r = Term.is_string (lhs r);;
 let is_right_build fs = Term.is_build fs <.> rhs;;
 let is_right_dummy r = Term.is_dummy (rhs r);;
 let is_right_flat r = Term.is_flat (rhs r);;
 let is_right_ground r = Term.is_ground (rhs r);;
 let is_right_linear r = Term.is_linear (rhs r);;
 let is_right_shallow r = Term.is_shallow (rhs r);;
 let is_right_string r = Term.is_string (rhs r);;

 let is_growing r =
  let l = lhs r in
  let check x = List.for_all ((>=) 1 <.> Pos.length) (Term.var_pos x l) in
  List.for_all check (List.intersect (Term.vars l) (Term.vars (rhs r)))
 ;;
 
 let matches r r' =
  try const true (E.match_problem [(lhs r,lhs r');(rhs r,rhs r')])
  with E.Not_matchable -> false
 ;;

 let is_variant r r' = matches r r' && matches r' r;;
 
 let subsumes = flip matches;;

 (*Every variable of l is also in r*)
 let is_nonerasing = uncurry List.is_subset <.> map Term.vars;;

 (*There is a variable in l that is not in r*)
 let is_erasing = not <.> is_nonerasing;;

 (*Every variable of r is also in l*)
 let is_right_nonerasing = uncurry List.is_supset <.> map Term.vars;;

 (*There is a variable in r that is not in l*)
 let is_right_erasing = not <.> is_right_nonerasing;;

 let is_rewrite_rule r = Term.is_fun (lhs r) && is_right_nonerasing r;;

 let is_contained = uncurry (flip E.contains);;

 let is_normal_form t r = try reducts t r = [] with Failure _ -> false;;
 let is_redex t r = E.matches t (lhs r);;
 
 (* Monadic Properties *)
 let is_overlap r p r1 =
  rename r >>= fun r' ->
  let unif = try E.are_unifiable (lhs r') (Term.subterm p (lhs r1))
             with Failure _ -> false in
  M.return (unif &&                                   (*TODO: check!*)
    (not (Pos.is_root p) || not (is_variant r' r1) || is_right_erasing r))
 ;;

 let ols_p r p r1 = 
  is_overlap r p r1 >>= fun b ->
  M.return (if b then [(r,p,r1)] else [])
 ;;

 let ols r ps r1 = M.flat_map (fun p -> ols_p r p r1) ps;;

 let overlaps ?(inner = true) ?(outer = true) r r1 =
  let ps0 = if inner then List.drop 1 (Term.funs_pos (lhs r1)) else [] in
  (* drop 1 will remove the root position; next we add it back if required *)
  let ps = if outer && Term.is_fun (lhs r1) then Pos.root::ps0 else ps0 in
  ols r ps r1;;
 let var_overlaps r r1 = ols r (Term.vars_pos (lhs r1)) r1;;

 let are_overlapping r r1 = 
  overlaps r r1 >>= fun ols -> 
  M.return (ols <> [])
 ;;

 let parallel_overlaps_p os r1 =
  M.map (fun (r,p) -> rename r >>= fun r' ->
         M.return (lhs r', Term.subterm p (lhs r1))) os >>= fun eq ->
  let unif = try const true (E.unify_problem eq)
             with Failure _       -> false
                | E.Not_unifiable -> false in
  let check = unif && match os with
   | [(r,p)] -> not (Pos.is_root p) || not (is_variant r r1) || is_right_erasing r
   | _ -> true in
  M.return (if check then [(os,r1)] else [])
 ;;

 let parallel_overlaps ?(inner = true) ?(outer = true) rs r1 =
  M.flat_map (fun r -> overlaps ~inner:inner ~outer:outer r r1) rs >>= fun os ->
  (* find non-empty combinations of mutually parallel overlaps: *)
  let rec go xs ys zs = match xs with
   | [] -> zs
   | (r',p,_)::xs ->
    let ys' = (r',p)::ys in
    ys'::go (List.filter (fun (_,p',_) -> Position.are_parallel p p') xs)
            ys' (go xs ys zs) in
  let oss = go os [] [] in
  if Term.is_linear (lhs r1) then M.return (List.map (fun os -> (os,r1)) oss)
  else M.flat_map (fun os -> parallel_overlaps_p os r1) oss
 ;;

 (* Miscellaneous *)
 let copy = id;;
 let hash r = Hashtbl.hash (map Term.hash r);;
 let depth = uncurry max <.> map Term.depth;;
 
 
 (* Equational Logic *)
 let apply_sub s = map (Sub.apply_term s);;
 
 (* Printers *)
 let fprintf fmt r =
  F.fprintf fmt "@[%a@ ->@ %a@]" Term.fprintf (lhs r) Term.fprintf (rhs r)
 ;;

 let fprintfm fmt r =
  F.fprintf fmt "@["; Term.fprintfm fmt (lhs r) >>= fun _ ->
  F.fprintf fmt "@ ->@ "; Term.fprintfm fmt (rhs r) >>= fun _ ->
  M.return (F.fprintf fmt "@]")
 ;;

 let to_string = F.flush_str_formatter <.> fprintf F.str_formatter;;

 let to_stringm r =
  fprintfm F.str_formatter r >>= (M.return <.> F.flush_str_formatter)
 ;; 
end
