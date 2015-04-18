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
module Automata = Automata.Default (Rewritingx);;
module A = Automata.Automaton;;
module C = Complexity;;
module F = Format;;
module G = Graph;;
module M = Automata.Monad;;
module P = Problem;;
module Perv = Pervasives;;
module S = Automata.Status;;
module T = Automata.Term;;
module XO = XmlOutput;;

module Initial = struct
 (*** MODULES *****************************************************************)
 module Initial = Automata.Initial;;
 module Lhs = Automata.Lhs;;
 module Path = Automata.Path;;

 (*** FUNCTIONS ***************************************************************)
 let (>>=) = M.(>>=);;
 let (>>) = M.(>>);;

 let rec transform s = function
  | T.Var _ -> s
  | T.State _ as t -> t
  | T.Fun (f,ts) -> T.Fun (f,List.map (transform s) ts)
 ;;

 let init f u =
  let cp = Path.fresh_reuse ~f:(const (const M.fresh_state)) in
  let fresh = const (M.liftM List.singleton M.fresh_state) in
  Initial.specific fresh cp [transform (T.Fun (f,[])) (T.of_term u)]
 ;;
end

module Completion = struct
 (*** MODULES *****************************************************************)
 module P = Automata.Path;;
 module State = Automata.State;;

 (*** TYPES *******************************************************************)
 type t = {
  automaton : A.t;
  compatible : bool;
  history : A.t;
  term : Term.t;
  steps : int;
  violations : (T.t * State.t) list;
 };;
 
 (*** FUNCTIONS ***************************************************************)
 let (>>=) = M.(>>=);;
 
 (* Evaluation Data Type *)
 let init u a n = {
   automaton = a;
   compatible = false;
   history = A.create 0;
   term = u;
   steps = n;
   violations = [];
 };;

 let get_automaton x = x.automaton;;
 let get_compatible x = x.compatible;;
 let get_h x = x.history;;
 let get_term x = x.term;;
 let get_steps x = x.steps;;
 let get_vs x = x.violations;;
 let set_automaton a x = {x with automaton = a};;
 let set_compatible x = {x with compatible = true};;
 let set_h a x = {x with history = a};;
 let set_term r x = {x with term = r};;
 let set_steps n x = {x with steps = n};;
 let set_vs vs x = {x with violations = vs};;

 (* Execution Functions *)
 let rec evaluate f x =
  if get_compatible x || get_steps x = 0 then M.return x else f x
 ;;
 
 (* Configuration Functions *)
 let paths qd trs x =
  let rec update = function
   | [] ->
    (if qd then A.quasi_det (get_automaton x) (* FIXME: >>= A.reduce *)
    else M.return (get_automaton x)) >>= fun a ->
    let modify a = if qd then a else A.ec a in
    A.minus (modify (A.copy a)) (get_h x) >>= fun h ->
    A.compatible ~h:(Some h) trs a >>= fun vs ->
    let x = set_automaton a (set_h (A.copy a) x) in
    if vs = [] then M.return (None,set_vs vs x)
    else M.return (Some (List.hd vs),set_vs (List.tl vs) x)
   | (t,p)::vs ->
    A.is_reachable t p (get_automaton x) >>= fun c ->
    if c then update vs else M.return (Some (t,p),set_vs vs x)
  in
  update (get_vs x)
 ;;
 
 let compute cp_trs qd trs x =
  paths qd trs x >>= fun (v,x) -> match v with
   | None -> M.return (set_compatible x)
   | Some (t,p) ->
    cp_trs t p (get_automaton x) >>= fun a ->
    M.return {x with automaton = a; steps = max ~-1 (get_steps x - 1)}
 ;;

 let arity trs =
  let max n f = M.find_ari f >>= (M.return <.> max n) in
  M.foldl max 1 (Trs.funs trs)
 ;;

 let plain cert trs =
  (* configuration *)
  arity trs >>= fun n -> 
  let cp_trs = P.tttbox ~p:true ~n:n P.fresh_max in
  let qd = not (Trs.is_left_linear trs) in
  (* computation *)
  let plain x =
   compute cp_trs qd trs x >>= fun x ->
   if get_compatible x && not cert && not (Trs.is_left_linear trs) then
    M.liftM (flip set_automaton x) (A.det (get_automaton x))
   else M.return x
  in
  let plain x = compute cp_trs qd trs x in
  M.return plain
 ;;
end

module Map = struct
 (*** MODULES *****************************************************************)
 module Term = struct
  type context = Hole | More of Function.t * context list;;
  type t = Term.t = Var of Variable.t | Fun of Function.t * t list;;

  let rec transform = function
   | Var _ -> Hole
   | Fun (f,ts) -> More (f,List.map transform ts)
  ;;

  let compare s = compare (transform s) <.> transform;;
  let fprintf = Term.fprintf;;
 end

 (*** INCLUDE *****************************************************************)
 include Map.Partial (Term);;
end

(*** TYPES ********************************************************************)
type flags = {
  help  : bool ref;
  iter  : int ref;
  steps : int ref;
  width : int ref;
  fpos  : bool ref;
  vpos  : bool ref;
  tree  : bool ref;
  tcap : bool ref;
  idem : bool ref;
  cert : bool ref;
};;
(* type proof = {map : A.t Map.t; cp : Term.t * Term.t * Term.t; status :
S.t};; *)
type aut = A.t * ((Automata.State.t * Automata.State.t) list option);;
type proof = {
  cp : Term.t list * Term.t * Term.t list;
  aut : (aut * aut) option;
  ptcap : bool;
  pidem : bool;
  ptree : bool;
};;
type t = P.t * proof;;
let make p proof = (p,proof);;

(*** GLOBALS ******************************************************************)
let code = "nonconfluence";;
let name = "Nonconfluence Processor";;
let keywords = ["confluence";"completion";"tree automata"];;

let flags = {
  help = ref false;
  iter = ref ~-1;
  steps = ref 2;
  width = ref ~-1;
  fpos = ref false;
  vpos = ref false;
  tcap = ref false;
  tree = ref false;
  idem = ref false;
  cert = ref false;
};;

let comment =
 "Checks if the given TRS admits a critical pair that is not joinable using \
  tree automata completion. If that is the case an empty problem is returned. \
  Otherwise the input problem remains unchanged."
;;

let spec =
 let spec = [
  ("--help",Arg.Set flags.help,"Prints information about flags.");
  ("-help",Arg.Set flags.help,"Prints information about flags.");
  ("-h",Arg.Set flags.help,"Prints information about flags.");
  ("-iter",Arg.Set_int flags.iter,
   "Specifies the maximum number of compatibility violations that should be \
    solved. This guarantees that the procedure always terminates. Otherwise \
    it might happen that non-confluence check does not terminate.");
  ("-steps",Arg.Set_int flags.steps,"Number of rewrite steps that are \
  performed from critical pairs to test terms nonconfluent [default: 2].");
  ("-width",Arg.Set_int flags.width,"Width of search tree for rewrite sequences; \
  -1 means unbounded [default: -1].");
  ("-fun",Arg.Clear flags.vpos,"use overlaps at function positions only.");
  ("-var",Arg.Clear flags.fpos,"use overlaps at variable positions only.");
  ("-tcap",Arg.Set flags.tcap,"show nonconfluence by tcap (default on).");
  ("-tree",Arg.Set flags.tree,"show nonconfluence by tree automata (default off).");
  ("-cert",Arg.Set flags.cert,"produce certifiable tree automata (default off).");
  ("-idem",Arg.Set flags.idem,"show nonconfluence by idem (default off).");
 ] in
 Arg.alignx 80 spec
;;

let help = (comment,keywords,List.map Triple.drop_snd spec);;

(*** FUNCTIONS ****************************************************************)
let (>>=) = M.(>>=);;
let (>>) = M.(>>);;
let init _ = 
 flags.help  := false;
 flags.iter  := ~-1;
 flags.steps := 2;
 flags.width := ~-1;
 flags.fpos  := true;
 flags.vpos  := true;
 flags.tree  := false;
 flags.tcap  := false;
 flags.idem  := false;
 flags.cert  := false;
;;
(* let make_proof m cp s = {map = m; cp = cp; status = s};; *)
let make_proof cp aut = {
  cp = cp;
  aut = aut;
  ptcap = !(flags.tcap);
  ptree = !(flags.tree);
  pidem = !(flags.idem);
};;

(* Destructors *)
let get_ip = fst;;
let get_proof = snd;;

let configuration trs =
 Completion.plain !(flags.cert) trs >>= fun f ->
 M.fresh_fun >>= fun g -> M.add_ari g 0 >>
 M.return (pair f (Initial.init g))
;;

let rec filter f m cps =
 let rec simplify xs = function
  | [] -> M.return (None,xs)
  | (s,o,t,cp)::cps ->
   let find u = Completion.get_automaton (Map.find u m) in
   let compatible u = Completion.get_compatible (Map.find u m) in
   let stopped u = Completion.get_steps (Map.find u m) = 0 in
   if stopped s && stopped t then simplify xs cps else
    A.inter (find s) (find t) >>= A.is_empty >>= fun c ->
    if c then
     if compatible s && compatible t then
(* FIXME delete
Format.printf "@\nfirst:@\n";
A.fprintfm Format.std_formatter (find s) >>= fun _ ->
Format.printf "@\nsecond:@\n";
A.fprintfm Format.std_formatter (find t) >>= fun _ ->
Format.printf "@\n%!";
*)
      M.return (Some (s,o,t,cp),[])
(* FIXME delete
)
*)
     else simplify ((s,o,t,cp)::xs) cps
    else simplify xs cps
 in
 simplify [] cps >>= fun (cp,cps) -> match cp with
  | Some cp -> M.return (Some cp,m)
  | None ->
   if cps = [] then M.return (None,m) else
    let replace u m x = M.return (Map.add u x m) in
    let evaluate u x m = Completion.evaluate f x >>= replace u m in
    Map.fold (fun u x m -> m >>= evaluate u x) m (M.return m) >>=
    flip (filter f) cps
;;

(*do not only consider critical pairs but also their reducts*)
let extend trs (s,o,t) = 
 let rs = Rewrite.sequences ~n:!(flags.steps) ~width:!(flags.width) s trs in
 let ts = Rewrite.sequences ~n:!(flags.steps) ~width:!(flags.width) t trs in
 List.map (fun (s,t) -> (s,o,t)) (List.product rs ts)
;;

let fresh_const = 
 M.lift (Monad.fresh_fun) >>= fun f ->
 M.lift (Monad.add_ari f 0) >>
 M.return (Term.Fun(f,[]))
;;

let fresh_var = M.lift (Monad.fresh_var) >>= fun x -> M.return (Term.Var x);;

let cache tbl k f = 
 if Hashtbl.mem tbl k then 
  M.return (Hashtbl.find tbl k)
 else
  f () >>= fun v ->
  Hashtbl.add tbl k v;
  M.return v
;;

let gen_sub tbl xs =
 M.foldl (fun s x -> 
  cache tbl x (fun _ -> fresh_const) >>= fun a ->
 M.return (Substitution.add x a s))
 (Substitution.empty) xs
;;

let grounding tbl t = 
 let xs = Term.vars t in
 gen_sub tbl xs >>= fun mu ->
 M.return (Substitution.apply_term mu t)
;;

let grounding_cps tbl ((s::_,o,t::_) as cp) =
 grounding tbl s >>= fun s ->
 grounding tbl o >>= fun o ->
 grounding tbl t >>= fun t ->
 M.return (s,o,t,cp)
;;

(* CUT & PASTE START *)
let make_cert trs a0 =
 let ll = Trs.is_left_linear trs in
 let qd = A.is_quasi_det a0 in
 if not (ll || qd) then failwith "[not certifiable]";
 if qd then
  let (a, ec) = A.qdet a0 in
  let a = A.map_trans Automata.Rhs.det a in
  if not (A.is_det a) then failwith "[not certifiable]";
  (a, Some ec)
 else (a0, None)
;;
(* CUT & PASTE END *)

let ncr_tree trs cps = 
 let tbl = Hashtbl.create 512 in
 M.map (grounding_cps tbl) cps >>= fun cps ->
 let us = List.foldl (fun us (s,o,t,_) -> s::t::us) [] cps in
 let us = List.unique ~c:Map.Term.compare us in
 (* configure computation *)
 configuration trs >>= fun (f,c) ->
 let init u a = Completion.init u a !(flags.iter) in
 let add m u a = M.return (Map.add u (init u a) m) in
 M.foldl (fun m u -> c u >>= add m u) Map.empty us >>= fun m ->
 filter f m cps >>= fun (cp,m) -> M.get >>= fun s -> match cp with
  | None -> M.return None
  | Some (s0,_,t0,(s,o,t)) ->
   M.map (grounding tbl) s >>= fun s ->
   M.map (grounding tbl) t >>= fun t ->
   grounding tbl o >>= fun o ->
   let cert a = if !(flags.cert) then make_cert trs a else (a, None) in
   let find u = cert (Completion.get_automaton (Map.find u m)) in
   let proof = make_proof (s,o,t) (Some (find s0,find t0)) in
   M.return (Some proof)
;;

let gen_sub xs = 
 M.foldl (fun s x -> 
  fresh_const >>= fun a -> 
 M.return (Substitution.add x a s))
 (Substitution.empty) xs
;;

let tcap s trs = M.lift (Trs.tcap s trs);;


let tcap trs (s::_,_,t::_) =
 let xs = List.unique (Term.vars s @ Term.vars t) in
 gen_sub xs >>= fun sigma -> (*replace variables by fresh constants*)
 let s = Substitution.apply_term sigma s in
 let t = Substitution.apply_term sigma t in
 tcap s trs >>= fun s' ->
 tcap t trs >>= fun t' ->
 M.return (not (Elogic.are_unifiable s' t'))
;;

let is_defined_term trs = function
 | Term.Fun (f,_) -> List.mem f (Trs.def_symbols trs)
 | _ -> false
;;

let rec strip_constructor trs s = function
 | Term.Fun (f,ts) as t when List.mem f (Trs.def_symbols trs) -> s = t
 | Term.Fun (f,[]) -> false
 | Term.Fun (f,ts) -> List.for_all (strip_constructor trs s) ts
 | Term.Var _ -> false
;;

let idem1 trs t = 
 (List.for_all (strip_constructor trs t) (Trs.reducts t trs))
;;

let idem trs (s::_,_,t::_) = 
 M.return (
  not (Term.equal s t) 
   && is_defined_term trs s && is_defined_term trs t
   && idem1 trs s && idem1 trs t
 )
;;

let rec mfind p = function
  | [] -> M.return None
  | l::ls -> p l >>= fun b -> if b then M.return (Some l) else mfind p ls
;;

let find f trs cps =
 mfind (f trs) cps >>= function
  | None -> M.return None
  | Some cp -> M.return (Some (make_proof cp None))
;;

let ncr_tcap trs cps = find tcap trs cps;;
let ncr_idem trs cps = find idem trs cps;;

let compute p =
 let trs = P.get_trs p in
 (if !(flags.fpos) then
  M.lift (Trs.overlaps trs trs) else M.return []) >>= fun ol1 ->
 (if !(flags.vpos) then 
  M.lift (Trs.var_overlaps trs) else M.return []) >>= fun ol2 ->
 let ol = ol1@ol2 in
 M.lift (Monad.map Trs.critical_peak ol) >>= fun cps ->
 let cps = List.flat_map (extend trs) cps in
 (
 if !(flags.tree) then ncr_tree trs cps
 else if !(flags.idem) then ncr_idem trs cps
 else (*if !(flags.tcap) then*) ncr_tcap trs cps
 (* else failwith "one of -tree -tcap or -idem needed" *)
 ) >>= fun proof ->
 M.return (Option.map (make p) proof)
;;

let (>>=) = Monad.(>>=);;
let (>>) = Monad.(>>);;

let solve fs p =
 let configurate s = F.printf "%s@\n%!" s; flags.help := true in
 (try init (); Arg.parsex code spec fs with Arg.Bad s -> configurate s);
 if !(flags.help) then (Arg.usage spec ("Options for "^code^":"); exit 0);
 if P.is_crp p then
  if !(flags.tcap) || P.for_all Trs.is_trs p then
   Monad.get >>= fun s ->
   let (p,s) = Either.right (M.eval (s,S.init) (compute p)) in
   Monad.set (fst s) >> Monad.return p
  else Monad.return None
 else Monad.return None
;;

(* Complexity Bounds *)
(* let complexity c _ = C.mul c C.other;; *)

(* Compare Functions *)
let equal p q = P.equal (get_ip p) (get_ip q);;

(* Printers *)
let fprintf fs fmt p =
 let proof = get_proof p in
 F.fprintf fmt "@[<1>%s:@\nterms: " name;
 Term.fprintfm fmt (List.hd (Triple.fst proof.cp)) >>= fun _ ->
 F.fprintf fmt " *<- ";
 Term.fprintfm fmt (Triple.snd proof.cp) >>= fun _ ->
 F.fprintf fmt " ->* ";
 Term.fprintfm fmt (List.hd (Triple.thd proof.cp)) >>= fun _ ->
 (* F.fprintf fmt "@\n@[<1>problem:@\n"; *)
 (* P.fprintfm fmt (get_op p) >>= fun _ -> *)
 F.fprintf fmt "@]@\n"; List.hd fs fmt >>= fun _ ->
 Option.fold (fun (sap,tap) ->
  let psi =
    let (>>=) = M.(>>=) in
    let go (a,p) =
      A.fprintfm fmt a >>= fun _ -> 
      Option.fold (fun ec ->
        F.fprintf fmt "@\n@[<1>precedence:@\n";
        List.iter (fun (l,r) ->
          F.fprintf fmt "%a -> %a@\n"
            Automata.State.fprintf l Automata.State.fprintf r
        ) ec;
        F.fprintf fmt "@]";
      ) () p;
      M.return ()
    in
    F.fprintf fmt "@\n@\n@[<1>first automaton:@\n";
    go sap >>= fun _ ->
    F.fprintf fmt "@]@\n@\n@[<1>second automaton:@\n";
    go tap >>= fun _ ->
    F.fprintf fmt "@]";
    M.return ()
  in
  let eval s = Either.right (M.eval (s,Automata.Status.init) psi) in
  Monad.update (fst <.> snd <.> eval)
 ) (Monad.return ()) (get_proof p).aut >>= fun _ ->
 Monad.return (F.fprintf fmt "@]")
;;

(* STUPID CUT & PASTE START *)
let fprintfx_state p = XO.node "state"
  [fun fmt -> Rewritingx.Monad.return (Automata.State.fprintf fmt p)];;

let fprintfx_lhs = function
  | Automata.Lhs.State p -> fprintfx_state p
  | Automata.Lhs.Fun (f, ps) ->
    XO.seq (Monad.fprintfx_fun f :: List.map fprintfx_state ps)
;;

let fprintfx_trans (l, r) = XO.node "transition" [
  XO.node "lhs" [fprintfx_lhs l];
  XO.node "rhs" [fprintfx_state r]]
;;

let fprintfx_automaton a = XO.node "treeAutomaton" [
  XO.node "finalStates" (List.map fprintfx_state (A.finals ~i:true a));
  let ts = A.fold (fun l -> Automata.Rhs.fold (List.cons <.> pair l)) a [] in
  XO.node "transitions" (List.map fprintfx_trans ts)]
;;
(* STUPID CUT & PASTE END *)

let fprintfx_compatibility = function
| None -> XO.node "compatibility" []
| Some ec ->
  XO.node "stateCompatibility" [
    XO.node "relation" (
      List.map (fun (l, r) ->
        XO.node "entry" [fprintfx_state l; fprintfx_state r]
      ) ec
    )
  ]
;;

let fprintfx fs p =
  let cp, trs = (get_proof p).cp, Problem.get_sw (get_ip p)  in
  XO.node "crDisproof" [
    XO.node "nonJoinableFork" [
      Sequence.fprintfx trs (Triple.snd cp :: List.rev (Triple.fst cp));
      Sequence.fprintfx trs (Triple.snd cp :: List.rev (Triple.thd cp));
      if (get_proof p).ptcap then XO.node "capNotUnif" [] else
      if (get_proof p).ptree then
        match (get_proof p).aut with | Some ((sa,sp),(ta,tp)) ->
        XO.node "emptyTreeAutomataIntersection" [
          XO.node "firstAutomaton" [
            fprintfx_automaton sa;
            XO.node "criterion" [fprintfx_compatibility sp]
          ];
          XO.node "secondAutomaton" [
            fprintfx_automaton ta;
            XO.node "criterion" [fprintfx_compatibility tp]
          ]
        ]
      else XO.node "magic" []
    ]
  ]
;;
