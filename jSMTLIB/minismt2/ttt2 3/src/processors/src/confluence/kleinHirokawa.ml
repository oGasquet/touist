(* Copyright 2013 Benjamin Höller, Bertram Felgenhauer
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
module C = Complexity;;
module F = Format;;
module Fun = Function;;
module P = Problem;;
module Var = Variable;;
module M = Automata.Monad;;

(*** TYPES ********************************************************************)
type flags = {
  help : bool ref;
  mace : bool ref;
  keep : bool ref;
 };;

type t = {
 ip : P.t;
 op : P.t;
 outputTRSS : Trs.t;
 outputTRST : Trs.t;
 pmace : bool;
}


(*** GLOBALS ******************************************************************)
let code = "kh";;
let name = "KH confluence processor";;
let keywords = ["klein";"hirokawa";"confluence"];;
let comment = "Confluence test for AC problems by using the theorem of Klein and
               Hirokawa.";;
let flags = {
  help = ref false;
  mace = ref false;
  keep = ref false;
};;

let spec =
 let spec = [
  ("--help",Arg.Set flags.help,"Prints information about flags.");
  ("-help",Arg.Set flags.help,"Prints information about flags.");
  ("-h",Arg.Set flags.help,"Prints information about flags.");
  ("-mace",Arg.Set flags.mace,"Use mace4 theorem prover if available.");
  ("-keep",Arg.Set flags.keep,"Keep mace4 temp files.");
  ] in
 Arg.alignx 80 spec
;;

let help = (comment,keywords,List.map Triple.drop_snd spec);;

(*** FUNCTIONS ****************************************************************)
let make ip op p s = {
 ip = ip;
 op = op;
 outputTRSS = p;
 outputTRST = s;
 pmace = !(flags.mace);
};;

let (>>=) = Monad.(>>=);;

(* Destructors *)
let get_ip p = p.ip;;
let get_op p = p.op;;
let get_outputTRSS p = p.outputTRSS;;
let get_outputTRST p = p.outputTRST;;

(* Compare Functions *)
let equal p q = P.equal (get_ip p) (get_ip q);;

(* Printers *)
(* Print critical pairs *)
let print_cp fmt (s,t) =
  Term.fprintfm fmt s >>= fun _ ->
  F.fprintf fmt " = ";
  Term.fprintfm fmt t >>= fun _ ->
  Monad.return ()
;;

let rec print_cps fmt cps =
 match cps with
  | [] -> Monad.return ()
  | [cp] ->
   print_cp fmt cp >>= fun _ ->
   F.fprintf fmt "@\n";
   Monad.return ();
  | cp::cps ->
   print_cp fmt cp >>= fun _ ->
   F.fprintf fmt ", ";
   print_cps fmt cps
;;

let fprintf_proof fmt p =
 F.fprintf fmt "@\nSplit input TRS into two TRSs S and T";
;;

let fprintf fs fmt p =
 F.fprintf fmt "@[<1>%s%a:@\n" name fprintf_proof p;
 (* Prints TRS S *)
 F.fprintf fmt "@\n@[<1>TRS S:@\n";
 Trs.fprintfm fmt (get_outputTRSS p) >>= fun _ ->
 (* Prints TRS T *)
 F.printf "@]@\n@\n@[<1>TRS T:@\n";
 Trs.fprintfm fmt (get_outputTRST p) >>= fun _ ->
 F.fprintf fmt "@]@\n@\n";
 F.fprintf fmt "As established above, T/S is terminating.@\n";
 F.fprintf fmt "T is strongly non-overlapping on S and S is strongly non-overlapping on T";
 Trs.critical_pairs ~inner:true ~outer:true (get_outputTRST p) (get_outputTRST p) >>= fun b ->
 if b <> [] then
  F.fprintf fmt "@\n@\n We get the following critical pairs, which are also S-critical pairs:@\n@\n";
 print_cps fmt b >>= fun _ ->
 if b <> [] then
  F.fprintf fmt "@\n all these critical pairs are joinable with S union T.";
 (* Message, if the theorem prover Prover9 or/and Mace4 is not installed. *)
 if p.pmace then (
  let rc = Sys.command "hash mace4 >/dev/null 2>&1" in
  if rc <> 0 then
   F.printf "@\n@\nPlease install theorem prover 'Prover9' and 'Mace4' for handling more TRSs."
  else if b <> [] then
   F.fprintf fmt "@\n@\n Mace4 did not detect other S-critical pairs."
  else
   F.fprintf fmt "@\n@\n Mace4 did not detect any S-critical pairs.";
 );
 F.fprintf fmt "@\n@\n All S-critical pairs are joinable.";
 F.fprintf fmt "@\n@\nWe have to check confluence of S.@]";
 Monad.iter (fun f -> F.fprintf fmt "@\n@\n"; f fmt) fs >>= fun _ ->
 Monad.return (F.fprintf fmt "@]")
;;

let fprintfx fs fmt p = failwith "Confluence.KleinHirokawa: certified output missing";;

(*** MODULES (part 2) *********************************************************)
(*** FUNCTIONS ****************************************************************)
let init _ =
 flags.help   := false;
 flags.mace   := false;
 flags.keep   := false;
;;

let contains s1 s2 =
 let re = Str.regexp s2 in try ignore(Str.search_forward re s1 0); true with Not_found -> false
;;

let rec writeQuantifier q_string element varList allOrExists =
 if varList <> [] then
  let var = List.nth varList element in
  Monad.to_string_var var >>= function varStr ->
  let q_string = if allOrExists then "all " ^ varStr ^ " " ^ q_string
                 else "exists " ^ varStr ^ " " ^ q_string in
  if element+1 < List.length varList then
   writeQuantifier q_string (element+1) varList allOrExists
  else
   Monad.return q_string
 else
  Monad.return ""
;;

let rec fillRulesToString str element ruleList =
 let rule = List.nth ruleList element in
 writeQuantifier "" 0 (Term.vars (Rule.lhs rule)) true >>= function quant ->
 Term.to_stringm (Rule.lhs rule) >>= fun first ->
 Term.to_stringm (Rule.rhs rule) >>= fun second ->
 let str = str ^
           quant ^ first ^ "=" ^ second
            ^ ".\n" in
 if element+1 < List.length ruleList then
  fillRulesToString str (element+1) ruleList
 else
  Monad.return str
;;

let fillString l1 l2P s =
 fillRulesToString "" 0 s >>= function left ->
 let quant_vars = List.unique (List.append (Term.vars l1) (Term.vars l2P)) in
 writeQuantifier "" 0 quant_vars false >>= function quant ->
 Term.to_stringm l1 >>= function first ->
 Term.to_stringm l2P >>= function second ->
 let right = first ^ "=" ^ second ^ ".\n" in
 let newString = "assign(max_seconds,5).\n" ^
                 "formulas(assumptions).\n" ^ left ^ "end_of_list.\n" ^
                 "formulas(goals).\n" ^ quant ^ right ^ "end_of_list.\n" in
 (* Remove () from constants *)
 let finalString = Str.global_replace (Str.regexp "()") "" newString in
 Monad.return finalString
;;

let theoremProver l1 l2 s0 =
 if !(flags.mace) then
  fillString l1 l2 (Trs.to_list s0) >>= function contentAsString ->
  let (tempname, hdl) = Filename.open_temp_file "csi." ".in" in
  output_string hdl contentAsString;
  close_out hdl;
  let rc = Sys.command ("mace4 < " ^ tempname ^ " > /dev/null 2>&1") in
  (* possible return codes: 127 - command not found; 0 - success; 5 - timeout *)
  if !(flags.keep) then
   Format.eprintf "---- mace4 < %s ---> %d <--- (exit code)@." tempname rc
  else
   Sys.remove tempname;
  Monad.return (rc = 0)
 else
  Monad.return false
;;

let kleinHirokawaCriterion t0 lin_t0 k =
 let trsT = Trs.of_list t0 in
 let trsS = Trs.diff k trsT in
 Trs.is_strongly_nonoverlapping2 trsT trsS >>= fun sno ->
 if sno then
  flip Monad.for_all (List.zip t0 lin_t0) (fun (rule1,rule3) ->
   flip Monad.for_all (List.zip t0 lin_t0) (fun (rule2,rule4) ->
    let funPos = Term.funs_pos (Rule.lhs rule2) in
    flip Monad.for_all funPos (fun p ->
     let l1 = Rule.lhs rule1 in
     let l2 = Rule.lhs rule2 in
     Term.rename l1 >>= fun l1' ->
     Term.rename l2 >>= fun l2' ->
     (* rules of linear TRS *)
     let l3 = Rule.lhs rule3 in
     let l4 = Rule.lhs rule4 in
     if Elogic.are_unifiable l3 (Term.subterm p l4) then
      (* strongly overlapping *)
      if Elogic.are_unifiable l1' (Term.subterm p l2') then
       (* MGU exists; compute the critical pair *)
       let sigma = Elogic.unify l1' (Term.subterm p l2') in
       let f = Substitution.apply_term sigma l2' in
       let u1 = Rule.rewrite f p rule1 in
       let u = Rule.rewrite f Position.root rule2 in
       Monad.return (Rewrite.are_joinable ~n:10 ~width:100 u1 u k)
      else
       (* strong overlap but no critical pair -> invoke theorem prover *)
       theoremProver l1' (Term.subterm p l2') trsS
     else
      Monad.return true
    )
   )
  ) >>= fun success ->
  Monad.return (success,trsT,trsS)
 else
  Monad.return (false,Trs.empty,Trs.empty)
;;

let rec
 splitTRSs k = function
 | [] -> Monad.return (false,Trs.empty,Trs.empty)
 | t0 :: ts -> 
  (* Splitting into TRS T and TRS S *)
  Trs.linearize (Trs.of_list t0) >>= fun linear_s ->
  let lin_t0 = Trs.to_list linear_s in
  let s0 = Trs.diff k (Trs.of_list t0) in
  if t0 = [] then
   (* All other combinations proved, all rules are in TRS S, that we dont need to check.
    Because S has to be confluent and therefore, we did no progress. *)
   splitTRSs k ts
  else
   kleinHirokawaCriterion t0 lin_t0 k >>= fun (success, new_T, new_S) ->
   if success then
    Monad.return (success, new_T, new_S)
   else
    splitTRSs k ts
;;

let startAlgorithm s k p =
 splitTRSs k s >>= fun (success, new_T, new_S) ->
 let op1 = P.set_trs new_S p in
 Monad.return (
  if success then
   Some (make p op1 new_S new_T)
  else
   None
 )
;;

let confluenceProof p nonTerminating =
 let fmt = F.std_formatter in
 let k = P.get_trs p in
 let candidates = Trs.to_list (Trs.diff k nonTerminating) in
 (* Avoid stack overflow *)
 if List.length candidates < 19 then
  if Trs.is_trs k then
   let allCombos = List.powerset candidates in
   (* commutative rules cannot occur in TRS T *)
   let s =  List.rev (List.sort List.compare_length allCombos) in
   (* S = [] is handled by other theorem, so eliminated *)
   (* Start with splittings with S as small as possible *)
   let s0 = List.diff (Trs.to_list k) (List.nth s 0) in
   if s0 = [] then
    startAlgorithm (List.drop 1 s) k p
   else
    startAlgorithm s k p
  else
   (* Failure: Not a TRS *)
   Monad.return None
 else
  (* Failure: Stack Overflow, too many list elements (2^(21)) *)
  Monad.return None
;;

let solve p =
 if P.is_auxp p && P.is_crp (P.get_inner_problem p) then
  confluenceProof (P.get_inner_problem p) (P.get_strict p)
 else
  Monad.return None
;;

let solve fs p =
 let configure s = F.printf "%s@\n%!" s; flags.help := true in
 (try init (); Arg.parsex code spec fs with Arg.Bad s -> configure s);
 if !(flags.help) then (Arg.usage spec ("Options for "^code^":"); exit 0);
 solve p
;;

