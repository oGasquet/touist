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
module XO = XmlOutput;;

(*** OPENS ********************************************************************)
open Util;;
open Rewritingx;;

(*** TYPES ********************************************************************)
type graph = Complete | Partial of Graph.t;;
type language = All | Constructor;;
type strategy = Full | Innermost | Outermost;;

type dp = {dps : Trs.t; trs : Trs.t; dg : graph; odps : Trs.t; otrs: Trs.t};;
type standard = Trs.t;;
type relative = {strict : Trs.t; weak : Trs.t};;
type confluence = Trs.t

type diagram = {orig: Trs.t; cstrict: Trs.t; cweak: Trs.t; cds: Diagram.t list;
 labeling: ((int -> Rewrite.step -> (int * Rewrite.step)) * int) list };;

type problem =
 | Cp of relative            (* complexity problem *)
 | Dp of dp                  (* dependency pair problem *)
 | Standard of standard      (* standard termination problem *)
 | Relative of relative      (* relative termination problem *)
 | Diagram of diagram        (* decreasing diagram problem with auxilliary relative termination problem *)
 | Confluence of confluence  (* confluence problem *)
 | AuxRT of aux              (* any problem with an auxilliary relative termination problem *)
and
 aux = {astrict : Trs.t; aweak : Trs.t; aproblem : problem}
;;

(* Note on AuxRT (and Diagram) problems:
 *
 * Since relatively terminating TRSs induce a reduction pair, it's
 * sometimes useful to decompose a TRS into a strict part that is
 * terminating to the remaining (weak) part. That is, given a TRS,
 * we want to identify the maximum set of rules that is terminating
 * relative to the rest.
 *
 * This is a perfect fit for rule removal processors: We simply set
 * up a termination problem for the TRS we're interested in. Then we
 * remove as many rules as possible. Every removed rule is terminating
 * relative to the rest. AuxRT does that, and allows switching back
 * to the original problem once the rule removal phase is done.
 *)

type t = {l : language; s : strategy; p : problem}

(*** FUNCTIONS ****************************************************************)
let (>>=) = M.(>>=);;

(* Constructors *)
let create_cp s w = Cp {strict = s; weak = w};;
let create_dp dps trs dg = Dp {dps = dps; trs = trs; dg = dg; odps = dps; otrs = trs};;
let create_sp trs = Standard trs;;
let create_rp s w = Relative {strict = s; weak = w};;
let create_ddp trs s w cds = 
 Diagram {orig = trs; cstrict = s; cweak = w; cds = cds; labeling = [];};;
let create_crp trs = Confluence trs
let make_cp l strategy s w = {l = l; s = strategy; p = create_cp s w};;
let make_sp l strategy trs = {l = l; s = strategy; p = create_sp trs};;
let make_rp l strategy s w = {l = l; s = strategy; p = create_rp s w};;
let make_ddp l strategy trs s w cds = 
 {l = l; s = strategy; p = create_ddp trs s w cds;}
;;
let make_aux s w p =
 {l = p.l; s = p.s; p = AuxRT {astrict = s; aweak = w; aproblem = p.p}}
;;
let make_crp l strategy trs =
 if l != All then
   failwith "Confluence problems with restricted start terms are not supported."
 else if strategy != Full then
   failwith "Confluence problems with strategies are not supported."
 else {l = l; s = strategy; p = create_crp trs}
;;
let make_dp l strategy dps trs dg =
 {l = l; s = strategy; p = create_dp dps trs dg}
;;
let sp_to_crp {l = l; s = s; p = Standard p} = {l = l; s = s; p = Confluence p};;

let fully_connected dps =
 let ns = Trs.to_list dps in
 List.foldl (fun g n -> Graph.add n ns g) Graph.empty ns
;;

let the_graph dps = function
 | Complete -> fully_connected dps
 | Partial p -> p
;;

let next_dg = function
 | {p = Dp p'} -> 
  if Trs.is_subset p'.dps p'.odps && Trs.is_subset p'.trs p'.otrs then p'.dg
  else Complete
 | _ -> failwith "not a DP problem"
;;

let set_trs trs p = match p with
 | {p = Standard _} -> {p with p = Standard trs}
 | {p = Dp p'} -> {p with p = Dp {p' with trs = trs}}
 | {p = Diagram p'} -> {p with p = Diagram {p' with orig = trs}}
 | {p = Confluence p'} -> {p with p = Confluence trs}
 | _ -> failwith "not a standard termination or DP problem"
;;

let set_dg dg dps trs p = match p with
 | {p = Dp p'} -> {p with p = Dp {p' with dg = dg; odps = dps; otrs = trs}}
 | _ -> failwith "not a dp problem"
;;

let update_dg dg p = match p with
 | {p = Dp p'} -> {p with p = Dp {p' with dg = dg;}}
 | _ -> failwith "not a dp problem"
;;

let set_dps dps p = match p with
 | {p = Dp p'} -> {p with p = Dp {p' with dps = dps}}
 | _ -> failwith "not a dp problem"
;;

let set_strict s p = match p with
 | {p = Cp p'} -> {p with p = Cp {p' with strict = s}}
 | {p = Relative p'} -> {p with p = Relative {p' with strict = s}}
 | {p = Diagram p'} -> {p with p = Diagram {p' with cstrict = s}}
 | {p = AuxRT p'} -> {p with p = AuxRT {p' with astrict = s}}
 | _ -> failwith "not a relative termination or CP problem"
;;

let set_weak w p = match p with
 | {p = Cp p'} -> {p with p = Cp {p' with weak = w}}
 | {p = Relative p'} -> {p with p = Relative {p' with weak = w}}
 | {p = Diagram p'} -> {p with p = Diagram {p' with cweak = w}}
 | {p = AuxRT p'} -> {p with p = AuxRT {p' with aweak = w}}
 | _ -> failwith "not a relative termination or CP problem"
;;

let set_sw s w p = match p with
 | {p = Cp _} -> {p with p = Cp {strict = s; weak = w}}
 | {p = Dp p'} -> {p with p = Dp {p' with dps = s; trs = w}}
 | {p = Standard _} ->
  if Trs.is_empty w then {p with p = Standard s}
  else failwith "not a standard termination problem"
 | {p = Relative _} -> {p with p = Relative {strict = s; weak = w}}
 | {p = Diagram p'} -> {p with p = Diagram {p' with cstrict = s; cweak = w}}
 | {p = AuxRT p'} -> {p with p = AuxRT {p' with astrict = s; aweak = w}}
 | {p = Confluence p'} ->
  if Trs.is_empty w then {p with p = Confluence s}
  else failwith "not a confluence problem"
;;

let set_cds cds p = match p with
 | {p = Diagram p'} -> {p with p = Diagram {p' with cds = cds}}
 | _ -> p
;;

let set_labeling lbl p = match p with
 | {p = Diagram p'} -> {p with p = Diagram {p' with labeling = lbl}}
 | _ -> failwith "not a diagram problem"
;;

let label_cds f i p = match p with
 | {p = Diagram p'} -> {p with p = Diagram {p' with
    cds = List.map (Diagram.label f i) p'.cds;
    labeling = (f, i) :: p'.labeling}}
 | _ -> failwith "not a diagram problem"
;;

(* add_cds uses the recorded labeling function and applies it to the new
   diagrams. *)
let add_cds cds p = match p with
 | {p = Diagram p'} ->
  let cds' = List.foldr (fun (lab,i) -> List.map (Diagram.label lab i)) cds
                        (p'.labeling) in
  {p with p = Diagram {p' with cds = List.rev_append (p'.cds) cds'}}
 | _ -> failwith "not a diagram problem"
;;

let set_language l p = {p with l = l};;
let set_strategy s p = {p with s = s};;
let adapt p' p = {p with p = p'};;

let minimize_dg dps = function
 | Complete -> Complete
 | Partial g -> Partial (Graph.filter_nodes (flip Trs.mem dps) g)
;;

let minimize p = match p with
 | {p = Dp p'} -> {p with p = Dp {p' with dg = minimize_dg p'.dps p'.dg}}
 | p -> p
;;

(* Access Functions *)
let get_inner_problem = function
 | {l = l; s = s; p = AuxRT p} -> {l = l; s = s; p = p.aproblem}
 | _ -> failwith "not a AuxRT problem"
;;

let rec get_trs = function
 | {p = Standard p} | {p = Confluence p} -> p
 | {p = Dp p} -> p.trs
 | {p = Diagram p} -> p.orig
 | {p = AuxRT _} as q -> get_trs (get_inner_problem q)
 | _ -> failwith "not a standard termination or DP problem"

let get_dg = function
 | {p = Dp p} -> p.dg
 | _ -> failwith "not a DP problem"
;;

let get_dps = function
 | {p = Dp p} -> p.dps
 | _ -> failwith "not a DP problem"
;;

let get_strict = function
 | {p = Cp p} | {p = Relative p} -> p.strict
 | {p = Diagram p} -> p.cstrict
 | {p = AuxRT p} -> p.astrict
 | _ -> failwith "not a relative termination or CP problem"
;;

let get_weak = function
 | {p = Cp p} | {p = Relative p} -> p.weak
 | {p = Diagram p} -> p.cweak
 | {p = AuxRT p} -> p.aweak
 | _ -> failwith "not a relative termination or CP problem"
;;

let get_sw = function
 | {p = Dp p} -> (p.dps,p.trs)
 | {p = Standard p} | {p = Confluence p} -> (p,Trs.empty)
 | {p = Cp p} | {p = Relative p} -> (p.strict,p.weak)
 | {p = Diagram p} -> (p.cstrict,p.cweak)
 | {p = AuxRT p} -> (p.astrict,p.aweak)
;;

let get_cds = function
 | {p = Diagram p} -> p.cds
 | _ -> failwith "not a diagram problem"
;;

let get_labeling = function
 | {p = Diagram p} -> p.labeling
 | _ -> failwith "not a diagram problem"
;;

let get_language p = p.l;;
let get_strategy p = p.s;;

(* Properties *)
let is_cp = function {p = Cp _} -> true | _ -> false;;
let is_dp = function {p = Dp _} -> true | _ -> false;;
let is_sp = function {p = Standard _} -> true | _ -> false;;
let is_rp = function {p = Relative _} -> true | _ -> false;;
let is_ddp = function {p = Diagram _} -> true | _ -> false;;
let is_auxp = function {p = AuxRT _} -> true | _ -> false;;
let is_crp = function {p = Confluence _} -> true | _ -> false;;
let is_ft = function {s = Full} -> true | _ -> false;;
let is_it = function {s = Innermost} -> true | _ -> false;;
let is_ot = function {s = Outermost} -> true | _ -> false;;
let is_al = function {l = All} -> true | _ -> false;;
let is_cl = function {l = Constructor} -> true | _ -> false;;

let is_empty_dg = function
 | Complete -> false
 | Partial g -> Graph.is_empty g
;;

let is_empty = function
 | {p = Dp p} -> Trs.is_empty p.dps || is_empty_dg p.dg
 | {p = Standard p} | {p = Confluence p} -> Trs.is_empty p
 | {p = Cp p} | {p = Relative p} -> Trs.is_empty p.strict
 | {p = Diagram p} -> 
  Trs.is_empty p.orig || (Trs.is_empty p.cstrict && p.cds = [])
 | {p = AuxRT _} -> false
;;

let for_all f = function
 | {p = Dp p} -> f p.dps && f p.trs
 | {p = Standard p} | {p = Confluence p} -> f p
 | {p = Cp p} | {p = Relative p} -> f p.strict && f p.weak
 | {p = Diagram p} -> f p.orig && f p.cstrict && f p.cweak
 | {p = AuxRT p} -> f p.astrict && f p.aweak
;;

let for_allm f = function
 | {p = Dp p} -> M.ite (f p.dps) f (M.return <.> const false) p.trs
 | {p = Standard p} | {p = Confluence p} -> f p
 | {p = Cp p} | {p = Relative p} ->
   M.ite (f p.strict) f (M.return <.> const false) p.weak
 | {p = Diagram _} -> failwith "for_allm not defined for Diagram problems"
 | {p = AuxRT _} -> failwith "for_allm not defined for AuxRT problems"
;;

let exists f = not <.> for_all (not <.> f);;
let existsm f = M.liftM not <.> for_allm (M.liftM not <.> f);;

(* Compare Functions *)
let equal_dg g g' = match (g,g') with
 | Complete, Complete -> true
 | Partial g, Partial g' -> Graph.equal g g'
 | _, _ -> false
;;

let rec equal p0 q0 = match (p0,q0) with
 | {p = Dp p}, {p = Dp q} ->
  Trs.equal p.dps q.dps && Trs.equal p.trs q.trs && equal_dg p.dg q.dg
 | {p = Standard p}, {p = Standard q} -> Trs.equal p q
 | {p = Cp p}, {p = Cp q} | {p = Relative p}, {p = Relative q} ->
  Trs.equal p.strict q.strict && Trs.equal p.weak q.weak
 (* | {p = Diagram p}, {p = Diagram q} -> *)
 | {p = Confluence p}, {p = Confluence q} -> Trs.equal p q
 | {p = AuxRT p}, {p = AuxRT q} ->
  Trs.equal p.astrict q.astrict && Trs.equal p.aweak q.aweak &&
  equal {p0 with p = p.aproblem} {q0 with p = q.aproblem}
 | _, _ -> false
;;

(* Printers *)
(* standard printers *)
let fprintf_dg fmt = function
 | Complete -> F.fprintf fmt "@[graph: fully connected@]"
 | Partial g -> F.fprintf fmt "@[<1>graph:@\n%a@]" Graph.fprintf g
;;

let rec fprintf ?(g = false) fmt = function
 | {p = Dp p} ->
  F.fprintf fmt "@[@[<1>DPs:@\n%a@]@\n@[<1>TRS:@\n%a@]"
   Trs.fprintf p.dps Trs.fprintf p.trs;
  if g then F.fprintf fmt "@\n%a@]" fprintf_dg p.dg
  else F.fprintf fmt "@]"
 | {p = Standard p} | {p = Confluence p} -> Trs.fprintf fmt p
 | {p = Cp p} | {p = Relative p} ->
  F.fprintf fmt "strict:@\n%a@\nweak:@\n%a" Trs.fprintf p.strict
   Trs.fprintf p.weak
 | {p = AuxRT p} as q ->
  F.fprintf fmt "strict:@\n%a@\nweak:@\n%a@\ninner:@\n@[<1>%a@]"
   Trs.fprintf p.astrict Trs.fprintf p.aweak (fprintf ~g:g) (get_inner_problem q)
 | {p = Diagram p} ->
  F.fprintf fmt "<diagram>"
;;

let to_string ?(g = false) =
 F.flush_str_formatter <.> fprintf ~g:g F.str_formatter
;;

(* monadic printers *)
let fprintfm_dg fmt = function
 | Complete -> M.return (F.fprintf fmt "@[graph: fully connected@]")
 | Partial g ->
  F.fprintf fmt "@[<1>graph:@\n";
  (if Graph.size_edges g > 1000 then M.return (F.fprintf fmt "...")
  else Graph.fprintfm fmt g) >>= fun _ ->
  M.return (F.fprintf fmt "@]")
;;

let rec fprintfm ?(g = false) fmt = function
 | {p = Dp p} ->
  F.fprintf fmt "@[@[<1>DPs:@\n"; Trs.fprintfm fmt p.dps >>= fun _ ->
  F.fprintf fmt "@]@\n@[<1>TRS:@\n"; Trs.fprintfm fmt p.trs >>= fun _ ->
  if g then (
   F.fprintf fmt "@]@\n"; fprintfm_dg fmt p.dg >>= fun _ ->
   M.return (F.fprintf fmt "@]")
  ) else M.return (F.fprintf fmt "@]@]")
 | {p = Standard p} | {p = Confluence p} -> Trs.fprintfm fmt p
 | {p = Cp p} | {p = Relative p} ->
  F.fprintf fmt "@[@[<1>strict:@\n"; Trs.fprintfm fmt p.strict >>= fun _ ->
  F.fprintf fmt "@]@\n@[<1>weak:@\n"; Trs.fprintfm fmt p.weak >>= fun _ ->
  M.return (F.fprintf fmt "@]@]")
 | {p = Diagram p} ->
  F.fprintf fmt "@[@[";
  (* F.fprintf fmt "<1>trs:@\n"; Trs.fprintfm fmt p.orig >>= fun _ -> *)
  F.fprintf fmt "@]@\n@[<1>strict:@\n"; Trs.fprintfm fmt p.cstrict >>= fun _ ->
  F.fprintf fmt "@]@\n@[<1>weak:@\n"; Trs.fprintfm fmt p.cweak >>= fun _ ->
  (* F.fprintf fmt "@]@\n@[<1>diagrams: (%d)" (List.length p.cds);   *)
   (* M.iter (fun d -> F.fprintf fmt "@\n"; Diagram.fprintfm fmt d) p.cds
   >>= fun _ -> *)
  F.fprintf fmt "@]@]";
  M.return ();
 | {p = AuxRT p} as q ->
  F.fprintf fmt "@[@[<1>strict:@\n"; Trs.fprintfm fmt p.astrict >>= fun _ ->
  F.fprintf fmt "@]@\n@[<1>weak:"; Trs.fprintfm fmt p.aweak >>= fun _ ->
  F.fprintf fmt "@]@\n@[<1>original problem:@\n";
  fprintfm ~g:g fmt (get_inner_problem q) >>= fun _ ->
  F.fprintf fmt "@]@]";
  M.return ();
;;

let to_stringm ?(g = false) p =
 fprintfm ~g:g F.str_formatter p >>= (M.return <.> F.flush_str_formatter)
;;

(* XML printers *)
let fprintfx_dg = function
  | Complete -> XO.node "graph" [XO.leaf "fullyConnected"]
  | Partial g -> XO.node "graph" [Graph.fprintfx g]
;;


let fprintfx_sig fs = XO.node "signature" (List.map 
          (fun f -> 
              XO.node "symbol" [
                M.fprintfx_fun f;
                (fun fmt -> M.find_ari f >>= fun i -> XO.int "arity" i fmt)
              ])
       fs)
;;

let fprintfx_cm p = 
    let trs = if is_cp p || is_rp p then Trs.union (get_strict p) (get_weak p)
         else if is_sp p then get_trs p
         else failwith "unsupported problem type for complexity measure"
       in 
    (if is_al p then XO.node "derivationalComplexity" [
       fprintfx_sig (Trs.funs trs)
     ]
    else if is_cl p then 
       XO.node "runtimeComplexity" [
         fprintfx_sig (Trs.con_symbols trs);
         fprintfx_sig (Trs.def_symbols trs)
     ]
    else failwith "unknown complexity measure")
;;

let fprintfx ?(g = false) = function
  | {p = Dp p} -> XO.seq [
    XO.node "dps" [Trs.fprintfx p.dps];
    XO.node "trs" [Trs.fprintfx p.trs];
    if g then fprintfx_dg p.dg
         else XO.id]
  | {p = Standard p} | {p = Confluence p} -> XO.node "trs" [Trs.fprintfx p]
  | {p = Relative p} -> XO.seq [
    XO.node "trs" [Trs.fprintfx p.strict];
    XO.node "trs" [Trs.fprintfx p.weak]]
  | {p = Cp p} -> XO.seq [
    XO.node "strict" [Trs.fprintfx p.strict];
    XO.node "weak"   [Trs.fprintfx p.weak]]
  | p -> if is_ddp p then XO.node "trs" [Trs.fprintfx (get_trs p)]
         else failwith "unsupport problem type for xml output"
;;

let to_stringx ?(g = false) p =
 fprintfx p F.str_formatter >>= (M.return <.> F.flush_str_formatter)
;;
