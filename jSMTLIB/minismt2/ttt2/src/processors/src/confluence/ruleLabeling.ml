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

(*** MODULES ******************************************************************)
module C = Complexity;;
module F = Format;;
module Fun = Function;;
module Number = Logic.Number;;
module P = Problem;;
module Var = Variable;;
module XO = XmlOutput;;
module O = Order;;

(*** TYPES ********************************************************************)
type flags = {
  help : bool ref;
  p : bool ref;
  strict : bool ref;
  weak : bool ref;
  left : bool ref;
  persist : bool ref;
};;
type t = {
 ip : P.t;
 op : P.t;
 rl : (Rule.t * int) list;
 pleft : bool;
 ppersist : bool;
};;
let make ip rl op l p = {
 ip = ip;
 op = op;
 rl = rl;
 pleft = l;
 ppersist = p;
};;

(*** GLOBALS ******************************************************************)
let code = "rule_labeling";;
let name = "Rule Labeling Processor";;
let keywords = ["rule labeling";"decreasing diagrams";"confluence"];;
let comment = "Implements rule labeling for decreasing diagrams.";;
let flags = {
  help = ref false;
  p    = ref false;
  strict = ref false;
  weak = ref false;
  left = ref false;
  persist = ref false;
};;

let spec =
 let spec = [
  ("--help",Arg.Set flags.help,"Prints information about flags.");
  ("-help",Arg.Set flags.help,"Prints information about flags.");
  ("-h",Arg.Set flags.help,"Prints information about flags.");
  ("-left",Arg.Set flags.left,"add labels left.");
  ("-p",Arg.Set flags.p,"Print encoding in SMT format and fail.");
  ("-strict",Arg.Set flags.strict,"strict decreasingness.");
  ("-weak",Arg.Set flags.weak,"weak decreasingness.");
  ("-persist",Arg.Set flags.persist,"use persistence. (experimental)");
  ] in
 Arg.alignx 80 spec
;;

let help = (comment,keywords,List.map Triple.drop_snd spec);;

let (>>=) = Monad.(>>=);;
(* Destructors *)
let get_ip p = p.ip;;
let get_op p = p.op;;
let get_rl p = p.rl;;
let get_left p = p.pleft;;
let get_persist p = p.ppersist;;

(* Complexity Bounds *)
let complexity c _ = C.mul c C.constant;;

(* Compare Functions *)
let equal p q =
 P.equal (get_ip p) (get_ip q) && P.equal (get_op p) (get_op q)
;;

(* Printers *)
let fprintf_rl fmt rl =
 Monad.iter (fun (rule,lab) -> 
  Format.fprintf fmt "@\n"; 
  Rule.fprintfm fmt rule >>= fun _ ->
  Format.fprintf fmt ": %d" lab;
  Monad.return ();) 
  rl
;;

let fprintf_left fmt b = 
 if b then Format.fprintf fmt "left" else Format.fprintf fmt "right";;

let fprintf fs fmt p =
 F.fprintf fmt "@[<1>%s:@\n" name; P.fprintfm fmt (get_op p) >>= fun _ ->
 F.fprintf fmt "@\n@[<1>rule labeling (%a):" fprintf_left (get_left p);
 fprintf_rl fmt (get_rl p) >>= fun _ ->
 F.fprintf fmt "@]@\n"; List.hd fs fmt >>= fun _ -> Monad.return (F.fprintf fmt "@]")
;;

let fprintfx fs p = XO.node "ruleLabeling" [P.fprintfx (get_op p); List.hd fs];;

(*** MODULES (part 2) *********************************************************)
type context = {
 arith              : Logic.arith;
 rtbl               : (Rule.t,Logic.a) Hashtbl.t;
};;

module Statex = struct type t = context end;;
module M = Util.Monad.Transformer.State (Statex) (Logic.Monad);;
open M;;

(*** FUNCTIONS ****************************************************************)
let (>>=) = M.(>>=);;
let (>>) = M.(>>);;
let init _ = 
 flags.help   := false;
 flags.strict := false;
 flags.weak   := false;
 flags.left   := false;
 flags.persist := false;
;;

let cache_m tbl f k = 
 if Hashtbl.mem tbl k then return (Hashtbl.find tbl k)
 else (f k >>= fun v -> (Hashtbl.add tbl k v; return v))
;;

(*Utilities*)
let big_add xs = List.foldl (<+>) Logic.zero xs;;
let bool b = if b then Logic.top else Logic.bot;;
(* functions lifted from Logic into M *)
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
let ($=$) = liftM2 (<=>);;
let ($+$) = liftM2 (<<>);;
let eval_a a ass = a >>= fun a -> lift (Logic.eval_a a ass);;
let eval_p p ass = p >>= fun p -> lift (Logic.eval_p p ass);;
let map_op op f ls = sequence (List.map f ls) >>= (return <.> op);;
let mapi_op op f ls = sequence (List.mapi f ls) >>= (return <.> op);;
let gen_op op f n = sequence (List.gen f n) >>= (return <.> op);;
let map_and f = map_op Logic.big_and f;;
let map_add f = map_op big_add f;;
let mapi_and f = mapi_op Logic.big_and f;;
let gen_and f = gen_op Logic.big_and f;;
let gen_add f = gen_op big_add f;;
let map_or f = map_op Logic.big_or f;;
let mapi_or f = mapi_op Logic.big_or f;;
let gen_or f = gen_op Logic.big_or f;;

(* Encodings *)
let var_rule rule = 
 get >>= fun c ->
 cache_m c.rtbl (fun _ -> fresh_arith) rule
;;

let var_step sel s =
 var_rule (Rewrite.step_get_rule s) >>= fun l ->
 let ls = O.lex (sel (Rewrite.step_get_lab s)) in
 M.return (l, ls)
;;

let lex_eq ls rs = ls >>= fun (l, _) -> rs >>= fun (r, rs) ->
 M.return ((l <=> r) <&> bool (O.is_eq rs))
;;

let lex_gt ls rs = ls >>= fun (l, _) -> rs >>= fun (r, rs) ->
 M.return (if !(flags.left)
  then (l <>> r) <|> ((l <=> r) <&> bool (O.is_gt rs))
  else bool (O.is_gt rs) <|> (bool (O.is_eq rs) <&> (l <>> r)))
;;

let fsts = List.map Triple.fst;;
let snds = List.map Triple.snd;;
let flips = List.map (fun (a,b,c) -> (b,a,c));;

let eq sel alpha s = lex_eq (var_step sel alpha) (var_step sel s);;
let gt sel alpha s = lex_gt (var_step sel alpha) (var_step sel s);;
let gt2 sel alpha beta s =
 gt (fsts <.> sel) alpha s $|$ gt (snds <.> sel) beta s;;

let join_strict alpha beta j = 
 let (ls,rs) = j in
 map_and (gt2 id alpha beta) (ls@rs)
;;

let seq_std_i sel alpha beta ss i _ = 
 let (ts,us) = List.split_at i ss in
 map_and (gt (fsts <.> sel) alpha) ts $&$
 (if us = [] then M.return Logic.top else
  (eq (snds <.> sel) beta (List.hd us) $|$ gt2 sel alpha beta (List.hd us)) $&$
  map_and (gt2 sel alpha beta) (List.tl us)
 )
;;

let seq_std sel alpha beta ss = 
 if ss = [] then M.return Logic.top else
 mapi_or (seq_std_i sel alpha beta ss) ss
;;


let join_std alpha beta (ls,rs) =
 seq_std id    alpha beta ls $&$
 seq_std flips beta alpha rs
;;

let join_weak d = 
 failwith "TODO";
;;


let encode_d e d = 
 let (l,r) = Diagram.peak d in (* TODO: par_peak? *)
 let js = Diagram.joins d in
 map_or (e l r) js
;;

let encode_persistence deps =
 map_and (fun (r,v,r') -> 
  if Term.count_var v (Rule.rhs r) <= 1 then M.return Logic.top else
  var_rule r $>$ var_rule r'
 ) deps
;;

let encode cds deps = 
 let e = 
  if !(flags.strict) then join_strict
  else if !(flags.weak) then join_weak 
  else join_std 
 in
 map_and (encode_d e) cds $&$
 Option.fold encode_persistence (M.return Logic.top) deps
;;

let context p = 
 {
 arith = Logic.nat (List.length (Trs.to_list (P.get_trs p)));
 rtbl = Hashtbl.create 512;
 }
;;

let decode_rule ass rule = 
 eval_a (var_rule rule) ass >>= fun lab ->
 M.return (rule,Logic.Number.to_int lab)
;;

let decode_rl ass p = 
 let trs = P.get_trs p in
 M.map (decode_rule ass) (Trs.to_list trs)
;;

let label_step left rl d _ s = 
 let lab r = List.assoc (Rewrite.step_get_rule r) rl in
 let (ls,r) = Diagram.par_peak d in
 let lls = List.map lab ls and lr = lab r and ls = lab s in
 let l = if List.exists (fun l -> l > ls) lls then O.GT else
         if List.exists (fun l -> l = ls) lls then O.EQ else O.NONE in
 let r = if lr > ls then O.GT else if lr = ls then O.EQ else O.NONE in
 (~-1,Rewrite.step_add_label ~left:left s (l,r,ls))
;;

let decode rl p = return (P.label_cds (label_step !(flags.left) rl) ~-1 p);;
 
let (>>==) = Monad.(>>=);;

let solve p =
 if P.is_ddp p then 
 let c = context p in
 (if !(flags.persist) then
  let trs = P.get_trs p in
  let strict = not (Trs.is_left_linear trs) && Trs.is_duplicating trs in
  Monad.liftM (fun x -> Some x) (Sorted.nested strict trs)
 else Monad.return None) >>== fun deps ->
 Monad.return (Logic.run ~obits:(-1) (
  M.run c (encode (P.get_cds p) deps >>= fun phi ->
  if !(flags.p) then (
   Format.fprintf Format.std_formatter "@[%a@]@\n" 
    (fun ppt -> Logic.fprintf_smt ppt) phi;
   return None
  ) else
  M.lift (Logic.solve ~solver:Logic.MiniSat phi) >>= function
   | None -> 
    M.return None
   | Some ass ->
    decode_rl ass p >>= fun rl ->
    decode rl p >>= fun p' -> 
    M.return (Some (make p rl p' !(flags.left) !(flags.persist)))
  )))
 else Monad.return None
;;

let solve fs p = 
 let configure s = F.printf "%s@\n%!" s; flags.help := true in
 (try init (); Arg.parsex code spec fs with Arg.Bad s -> configure s);
 if !(flags.help) then (Arg.usage spec ("Options for "^code^":"); exit 0);
 if !(flags.strict) && !(flags.weak) then 
  (Arg.usage spec (code^": -strict and -weak are not allowed"));
 solve p 
;;

