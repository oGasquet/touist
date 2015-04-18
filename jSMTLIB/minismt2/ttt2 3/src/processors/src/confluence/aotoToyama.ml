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
  theorem : int ref;
  bound : int ref;
 };;

type t = {
 ip : P.t;
 op : P.t;
 outputTRSP : Trs.t;
 outputTRSS : Trs.t;
 completeTRS : Trs.t;
 ptheorem : int;
}


(*** GLOBALS ******************************************************************)
let code = "at";;
let name = "AT confluence processor";;
let keywords = ["Aoto";"Toyama";"confluence"];;
let comment = "Confluence test for AC problems by using the theorems of Aoto and Toyama.";;
let flags = {
  help = ref false;
  theorem = ref 0;
  bound = ref 0;
};;

let spec =
 let spec = [
  ("--help",Arg.Set flags.help,"Prints information about flags.");
  ("-help",Arg.Set flags.help,"Prints information about flags.");
  ("-h",Arg.Set flags.help,"Prints information about flags.");
  ("-theorem",Arg.Set_int flags.theorem,"Indicates which of the three theorems is used.
                                         By default theorem 3 will be used.");
  ("-b",Arg.Set_int flags.bound,"Indicates an upper bound for the number of rewrite rules.
                                 If the number of rewrite rules is >= b, then the processor
                                 ends. By default b = 12 will be used.");
  ("-bound",Arg.Set_int flags.bound,"Indicates an upper bound for the number of rewrite rules.
                                 If the number of rewrite rules is >= b, then the processor
                                 ends. By default b = 12 will be used.");
  ] in
 Arg.alignx 80 spec
;;

let help = (comment,keywords,List.map Triple.drop_snd spec);;

(*** FUNCTIONS ****************************************************************)
let make ip op p s t cpc = {
 ip = ip;
 op = op;
 outputTRSP = p;
 outputTRSS = s;
 completeTRS = t;
 ptheorem = cpc;
};;

let (>>=) = Monad.(>>=);;
(* Destructors *)
let get_ip p = p.ip;;
let get_op p = p.op;;
let get_outputTRSP p = p.outputTRSP;;
let get_outputTRSS p = p.outputTRSS;;
let get_completeTRS p = p.completeTRS;;
let get_ptheorem p = p.ptheorem;;

(* Compare Functions *)
let equal p q =
 P.equal (get_ip p) (get_ip q) && P.equal (get_op p) (get_op q)
;;

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

let print_proof_cp fmt pUpINV trsS output_cp =
 (* Prints CPs *)
 F.printf "@\n@\n CP(S,S) = @\n";
 Trs.critical_pairs ~inner:true ~outer:true trsS trsS >>= fun b ->
 print_cps fmt b >>= fun _ ->
 F.printf "@\n CP(S,P union P^-1) = @\n";
 Trs.critical_pairs ~inner:true ~outer:true trsS pUpINV >>= fun c ->
 print_cps fmt c >>= fun _ ->
 if output_cp = 3 then
  begin
   F.printf "@\n CP(P union P^-1,S) = @\n";
   Trs.critical_pairs ~inner:true ~outer:true pUpINV trsS >>= fun d ->
   print_cps fmt d
  end
 else if output_cp = 2 then
  begin
   F.printf "@\n@\n PCP_in(P union P^-1,S) = @\n";
   Trs.parallel_critical_pairs ~inner:true ~outer:false pUpINV trsS >>= fun d ->
   print_cps fmt d
  end
 else
  begin
   F.printf "@\n@\n CP_in(P union P^-1,S) = @\n";
   Trs.critical_pairs ~inner:true ~outer:false pUpINV trsS >>= fun d ->
   print_cps fmt d
  end
;;

let fprintf_proof fmt p =
 F.fprintf fmt "@\nComplete TRS T' of input TRS";
;;

let fprintf fs fmt p =
 F.fprintf fmt "@[<1>%s%a:@\n" name fprintf_proof p;
 Trs.fprintfm fmt (get_completeTRS p) >>= fun _ ->

 (* Prints complete TRS of input TRS*)
 F.fprintf fmt "@\n@\n T' = (P union S) with";

 (* Prints reversible TRS P *)
 F.fprintf fmt "@\n@\n TRS P:";
 Trs.fprintfm fmt (get_outputTRSP p) >>= fun _ ->

 (* Prints terminating TRS S *)
 F.printf "@\n@\n TRS S:";
 P.fprintfm fmt (get_op p) >>= fun _ ->

 let output_cp = get_ptheorem p in
 let trsS = get_outputTRSS p in
 let trsP = get_outputTRSP p in
 let pUpINV = Trs.union trsP (Trs.invert trsP) in

 if output_cp = 3 then
  F.fprintf fmt "@\n@\nS is linear and P is reversible."
 else
  F.fprintf fmt "@\n@\nS is left-linear and P is reversible.";

 (* Prints Critical pair sets *)
 print_proof_cp fmt pUpINV trsS output_cp >>= fun _ ->
 F.fprintf fmt "@\n@\nWe have to check termination of S:@\n";
 F.fprintf fmt "@]@\n"; List.hd fs fmt >>= fun _ ->
 Monad.return (F.fprintf fmt "@]")
;;

let fprintfx fs fmt p = failwith "Confluence.AotoToyama: certified output missing";;

(*** MODULES (part 2) *********************************************************)
(*** FUNCTIONS ****************************************************************)
let init _ =
 flags.help   := false;
;;

module AotoToyama = struct
 include Rewrite;;

 (* check whether u -S->^* -?-> <-S-^* v, where -?-> = -->_P or -||->_P
  * depending on the flag [par]. At this point, P = P^-1. *)
 let are_joinable_two_TRS ?(n = ~-1) u v trsS trsP par =
  (* reducts of term v including the term itself *)
  let redV = v :: reducts ~n:n v trsS in
  (* reducts of term u *)
  let redU = u :: reducts ~n:n u trsS in
  let middle = if par then parallel trsP else fun t -> t :: reducts ~n:1 t trsP in
  u = v or
  List.intersect (List.flat_map middle redU) redV <> []
 ;;

 (** [calculate_new_rules cpList lToR s0 p0 parallel] checks if the critical pairs in [cpList]
 are joinable with arbitrary steps in trs s0 and one parallel step in p0 (if parallel = true). If parallel
 = false, then instead of the parallel step a single rewrite step will be made. If a critical
 pair is not joinable, the function returns new rules, which have to be added for making
 the critrical pairs joinable. The calculation of the new rules depends on lToR. If lToR is true, then the
 new rule goes from the left hand side of the critical pair to the normalform of the right hand side of the
 critical pair. If lToR is false, the new rule goes from the right hand side of the critical pair to the
 normalform of the left hand side of the critical pair.*)

 let calculate_new_rule leftToNFR s0 p0 parallel cp =
  let (n_lhs,n_rhs) = if leftToNFR then cp else Pair.flip cp in
  if are_joinable_two_TRS ~n:10 n_lhs n_rhs s0 p0 parallel
  then []
  else [Rule.of_terms n_lhs (find_normalform ~n:10 n_rhs s0)]
 ;;

 let calculate_new_rules cpList leftToNFR s0 p0 parallel =
  Trs.of_list (List.flat_map (calculate_new_rule leftToNFR s0 p0 parallel) cpList)
 ;;

 (** [calculate_new_rules_nl_to_nr cpList s0 p0 parallel] checks if the critical pairs in [cpList]
 are joinable with arbitrary steps in trs s0 and one parallel step in p0. If parallel
 = false, then instead of the parallel step a single rewrite step will be made.
 If a critical pair is not joinable, the function returns new rules, which have to be added for making
 the critrical pairs joinable. The new rules goes from the normalform of one side of a critical
 pair to the normalform of the other side. A rewrite rule check is included.
 In addition, we check that the new rules are derivable from p0 *)

 let calculate_new_rule_nl_to_nr s0 p0 parallel cp =
  if are_joinable_two_TRS ~n:10 (Pair.fst cp) (Pair.snd cp) s0 p0 parallel
  then []
  else
   (* Normalform of lhs of cp *)
   let l = Rewrite.find_normalform ~n:10 (Pair.fst cp) s0 in
   (* Normalform of rhs of cp *)
   let r = Rewrite.find_normalform ~n:10 (Pair.snd cp) s0 in
   (* add l -> r and r -> l if they are valid rules and derivable using p0 steps *)
   let ruleCheck r =
    Rule.is_rewrite_rule r &&
    Rewrite.is_reachable ~n:10 (Rule.lhs r) (Rule.rhs r) p0 in
   List.filter ruleCheck [Rule.of_terms l r; Rule.of_terms r l]
 ;;

 let calculate_new_rules_nl_to_nr cpList s0 p0 parallel =
  Trs.of_list (List.flat_map (calculate_new_rule_nl_to_nr s0 p0 parallel) cpList)
 ;;

 let check_joinability cpList s0 p0 parallel =
  flip List.for_all cpList (fun cp ->
   are_joinable_two_TRS ~n:10 (Pair.fst cp) (Pair.snd cp) s0 p0 parallel)
 ;;

 open Monad;;

 (** [parallel_with_cond trs var t] returns reducts of [t] with one parallel step. Checks the variable condition. *)

 (* parallel steps with variable condition: any variable occuring in the reduct below a rewrite
  * position must be a member of 'var' *)
 let parallel_with_v_cond trs var t = match t with
  | Term.Var _ -> [t]
  | Term.Fun (f,ts) ->
   let tss = List.times (List.map (parallel trs) ts) in
   let rs = List.map (fun ts -> Term.Fun (f,ts)) tss in
   let tm = Trs.rewrite t Position.root trs in
   List.unique_hash (List.filter (fun t -> List.diff (Term.vars t) var = []) tm @ rs)
 ;;

 (** [are_joinable_two_TRS ~s:s ~n:n u v r p par var] checks if the terms [u] and [v] are
 joinable within [n] steps of TRS [r] and one parallel rewrite step of TRS [p] (if par = true)
 or with a single rewrite step  of TRS [p] (if par = false), using the rewrite strategy [s].
 If [n] is smaller than [0] this function may not terminate. Per default [s = Full] and [n = ~-1].
 Includes a variable condition (only in par = true).*)

 let are_joinable_two_TRS_with_v_cond ?(s = Full) ?(n = ~-1) u v trsS trsP par var =
  (* reducts of term v including the term itself *)
  let redV = v :: reducts ~n:n v trsS in
  (* reducts of term u *)
  let redU = reducts ~n:n u trsS in
  let middle = if par then parallel_with_v_cond trsP var else fun t -> t :: reducts ~n:1 t trsP in
  u = v or
  List.intersect (List.flat_map middle redU) redV <> [] or
  List.intersect redU (List.flat_map middle redV) <> []
 ;;

 (** [calculate_new_rules_with_v_cond cpList leftToNFR s0 p0 parallel varList] checks if the critical pairs in [cpList]
 are joinable with arbitrary steps in trs s0 and one parallel step in p0 (if parallel = true). If parallel
 = false, then instead of the parallel step a single rewrite step will be made. If a critical
 pair is not joinable, the function returns new rules, which have to be added for making
 the critrical pairs joinable. The calculation of the new rules depends on lToR. If lToR is true, then the
 new rule goes from the left hand side of the critical pair to the normalform of the right hand side of the
 critical pair. If lToR is false, the new rule goes from the right hand side of the critical pair to the
 normalform of the left hand side of the critical pair. The argument varList contains for every critical pair
 a list of variables, with which the variable condition will be realized.*)

 let calculate_new_rule_with_v_cond leftToNFR s0 p0 parallel (cp,varList) =
  let (n_lhs,n_rhs) = if leftToNFR then cp else Pair.flip cp in
  if are_joinable_two_TRS_with_v_cond ~n:10 n_lhs n_rhs s0 p0 parallel varList
  then []
  else [Rule.of_terms n_lhs (find_normalform ~n:10 n_rhs s0)]
 ;;

 let calculate_new_rules_with_v_cond cpList leftToNFR s0 p0 parallel varLists =
  Trs.of_list (List.flat_map (calculate_new_rule_with_v_cond leftToNFR s0 p0 parallel) (List.zip cpList varLists))
 ;;

 (** [add_rules l term k] The list [l] is a term list which contains possible rhs of a new rule. The function
 checks if a term and the rhs of [l] just exists in [k]. If it not exist, so the rule will be added to this TRS [k]. *)

 (*
 (* XXX: the loops below only work if the new rules are appended to the Trs list *)
 let add_rules_term l _ term k =
  let new_rules = List.map (Rule.of_terms term) l in
  Trs.unique (Trs.union k (Trs.of_list new_rules))
 ;;
 *)

 let add_rules_term l term k =
  List.foldl (fun k rhs ->
   if List.mem (Rule.of_terms term rhs) (Trs.to_list k) then   
    (* Rule already exists *)
    k
   else
    Trs.add (Rule.of_terms term rhs) k
  ) k l
 ;;

 (** [improve p k] checks all rhs of the rules in [k] if we can perform a rewrite step on TRS [p].
 If we can perform, then we eliminate the old rule and add a new rule, which has the same lhs but a new rhs. The new rhs is
 constructed after a rewrite step on TRS [p] on the old rhs.  *)

 let improve p rule =
  if reducts ~n:1 (Rule.rhs rule) (Trs.of_list p) <> [] then
   let smallK = Trs.empty in
   Trs.to_list (add_rules_term (reducts ~n:1 (Rule.rhs rule) (Trs.of_list p)) (Rule.lhs rule) smallK)
  else
   [rule]
 ;;

 (** [minimize_with_improvement rules s0 p0 imprRules] checks all rules in [rules], if they can be omitted using
 the improved rules. A rule can be omitted, if the other rules do the same 'step' as the rule does.
 The function checks if with all improved rules in [imprRules] except the improved rule we come from the lhs of
 the rule of [rules] to its rhs.*)

 (*
 avoid variants of AC rules:
 f(x,f(y,z)) -> f(f(x,y),z) ... + f(x,f(y,z)) -> f(z,f(x,y)), f(f(z,x),y) ...
 *)

 let minimize_with_improvement rules s0 p0 imprRules =
  Pair.snd (List.foldl (fun (imprRules, newK) rule ->
   let imprRule = improve (Trs.to_list p0) rule in
   let smallerList = List.diff imprRules imprRule in
   (* right_side = all terms of the form  (rhs ->*_S -||->_P) *)
   let rhsRed = reducts ~n:10 (Rule.rhs rule) (Trs.of_list (List.append smallerList (Trs.to_list s0))) in
   let parallelStep = List.map (parallel p0) rhsRed in
   let right_side = List.unique (List.flatten parallelStep) in
   let lhsRed = reducts ~n:10 (Rule.lhs rule) (Trs.of_list (List.append smallerList (Trs.to_list s0))) in
   let left_side = List.unique (List.append lhsRed [Rule.lhs rule]) in
   (* a new rule does not make sense *)
   if List.intersect left_side right_side <> [] then
     (smallerList, newK)
   else
    if imprRule = [rule] then
      (imprRules, List.append newK [rule])
    else
     let imprK = List.append newK (List.diff (List.unique imprRule) [rule]) in
     (imprRules, imprK)
  ) (imprRules, []) rules)
 ;;

 (** [minimize_new_rules rules trs] checks all rules in [rules], if they can be omitted. A rule can be omitted,
 if the other rules do the same 'step' as the rule does.
 The function checks if with all rules in [rules] except the rule of [rules] (in the following
 called 'problematic rule') we come from the lhs of the problematic rule to the rhs of the problematic rule.*)

 let minimize_new_rules rules trs =
  List.foldl (fun rules rule ->
   let smallerList = List.diff rules [rule] in
   (* Old TRS including new rules. *)
   let newTRS = Trs.of_list (List.append smallerList (Trs.to_list trs)) in
   let rhsRED = reducts ~n:10 (Rule.rhs rule) newTRS in
   let lhsRED = reducts ~n:10 (Rule.lhs rule) newTRS in
   if List.intersect lhsRED (List.append rhsRED [Rule.rhs rule]) <> [] then
    (* Rule not needed, can be ignored. Check next rule *)
    smallerList
   else
    (* Rule needed, check next rule. *)
    rules
  ) rules rules
 ;;

 (** [preprocessing rules nonTerm] checks all rules in [rules] if there exists
 a (some) non-terminating rule(s) and if there exists a (some) left linear (linear if
 'linear ' is true) rules. The function stores all non-terminating and non (left) linear
 rules in nonTerminatingRules and it returns them. We say that a rewrite rule is
 non-terminating, if it is a commutative rule or a rule, where its lhs is a subterm of its rhs. *)

 let preprocessing rules linear =
  flip List.filter rules (fun rule ->
   (* True, if rule is a commutative rule *)
   let isComRule = is_reachable ~s:Full ~n:10 (Rule.rhs rule) (Rule.lhs rule) (Trs.of_list [rule]) in
   (* True, if lhs of rule is a subterm of its rhs *)
   let isSubTerm = Term.is_subterm (Rule.lhs rule) (Rule.rhs rule) in
   let isLinear = if linear then Rule.is_linear rule
                  else Rule.is_left_linear rule in
   isComRule or isSubTerm or not isLinear
  )
 ;;

 (* get variables below rewrite positions from a PCP *)
 let getVariables (ls,r) =
  List.unique (List.flat_map (fun (_,p) -> Term.vars (Term.subterm p (Rule.lhs r))) ls)
 ;;

 (* Main improvement of AC-Rules *)
 let improvement2 p k =
  flip List.flat_map k (fun rule ->
   if Rewrite.reducts ~n:1 (Rule.rhs rule) (Trs.of_list p) <> [] then
    (* Apply a rewrite step of TRS P on the rhs of the rule *)
    let n_rhs = Rewrite.reducts ~n:1 (Rule.rhs rule) (Trs.of_list p) in
    (* Get a new rule, with the old lhs and the new rhs and add it to existing rules*)
    Trs.to_list (add_rules_term n_rhs (Rule.lhs rule) Trs.empty)
   else
    [] (* XXX: should this be [rule] ? *)
  )
 ;;

 (* Improvement 2a of AC-Rules *)
 let improvement2a s p k =
  Monad.foldl (fun k rule ->
   let pUpINV = Trs.of_list (List.append p (Trs.to_list (Trs.invert (Trs.of_list p)))) in
   Trs.critical_pairs ~inner:true ~outer:false pUpINV (Trs.of_list [rule]) >>= fun b ->
   if b = [] || Rewrite.reducts ~n:1 (Rule.rhs rule) (Trs.of_list p) = [] then
    Monad.return k
   else
    let elimRule = Trs.of_list (List.diff (Trs.to_list k) [rule]) in
    (* Apply a rewrite step of TRS P on the rhs of the rule *)
    let n_rhs = Rewrite.reducts ~n:1 (Rule.rhs rule) (Trs.of_list p) in
    (* Get a new rule, with the old lhs and the new rhs and add it to existing rules,
       after eliminating the rule with the old rhs *)
    let n_rules = add_rules_term n_rhs (Rule.lhs rule) elimRule in
    Monad.return n_rules
  ) k s
 ;;

 (* Improvement 2b of AC-Rules *)
 let improvement2b cpset s0 k =
  Monad.foldl (fun k cp ->
   let nf_rhs = Rewrite.find_normalform ~n:10 (Pair.snd cp) s0 in
   if nf_rhs <> Pair.snd cp then
    let n_rules = add_rules_term [nf_rhs] (Pair.fst cp) k in
    Monad.return n_rules
   else
    Monad.return k
  ) k cpset
 ;;

 let criticalPairCondition pUpINV s0 theorem =
  if theorem = 1 then 
   Trs.critical_pairs ~inner:true ~outer:false pUpINV s0 >>= fun b ->
   Monad.return (b = [],b)
  else if theorem = 2 then
   let pcp o = Trs.parallel_critical_peak o >>= fun (t,_,u) -> Monad.return (t,u) in
   Trs.parallel_overlaps ~inner:true ~outer:false pUpINV s0 >>= fun ols ->
   (* all variables on the parallel positions are stored in variablesX *)
   let v = List.map getVariables ols in
   Monad.map pcp ols >>= fun b ->
   (* all parallel critical pairs *)
   (* PCP(P U P^{-1},S) should be joinable occuring to variable condition *)
   let joinable = calculate_new_rules_with_v_cond b true s0 pUpINV true v = Trs.empty in
   Monad.return (joinable,b)
  else (* theorem = 3 *) 
   Trs.critical_pairs ~inner:true ~outer:true pUpINV s0 >>= fun b ->
   (* CP(P U P^{-1},S) should be joinable*)
   let joinable = calculate_new_rules b true s0 pUpINV false = Trs.empty in
   Monad.return (joinable,b)
 ;;

 let rec checkConfluence_inner s0 k theorem upBound =
  let p0 = List.diff (Trs.to_list k) s0 in
  let s0 = Trs.of_list s0 in
   (* For all theorems: check whether P is reversible *)
   if List.for_all (fun h -> Rewrite.is_reversible h (Trs.of_list p0)) p0 then 
    begin
     let pUpINV = Trs.of_list (List.append p0 (Trs.to_list (Trs.invert (Trs.of_list p0)))) in
     let parallelFlag = if theorem = 3 then false else true in
     let linearCheck = if theorem = 3 then true else false in
     criticalPairCondition pUpINV s0 theorem >>= fun condition1 ->
     if Pair.fst condition1 then
      begin
       Trs.critical_pairs ~inner:true ~outer:true s0 pUpINV >>= fun b ->
       (* CP(S,P U P^{-1}) should be joinable *)
       if calculate_new_rules b false s0 pUpINV parallelFlag = Trs.empty then
        Trs.critical_pairs ~inner:true ~outer:true s0 s0 >>= fun b ->
        (* CP(S,S) should be joinable *)
        if check_joinability b s0 pUpINV parallelFlag then
         Monad.return (true, s0, Trs.of_list p0)
        else
         (* CP(S,S) not joinable - look for new rules *)
         let n_rules = calculate_new_rules_nl_to_nr b s0 pUpINV parallelFlag in
         if n_rules <> Trs.empty then
          (* and minimize them *)
          look_for_new_rules k s0 p0 pUpINV n_rules linearCheck theorem upBound
         else
          Monad.return (false, Trs.empty, Trs.empty)
       else
        (* CP(S,P U P^{-1}) not joinable - look for new rules *)
        let n_rules = calculate_new_rules b false s0 pUpINV parallelFlag in
        look_for_new_rules k s0 p0 pUpINV n_rules linearCheck theorem upBound
      end
     else
      if theorem = 2 then 
       begin
        (* PCP(P U P^{-1},S) not joinable occuring to variable condition *)
        (* We look for new rules *)
        Trs.parallel_overlaps ~inner:true ~outer:false pUpINV s0 >>= fun ols ->
        (* all variables on the parallel positions are stored in variablesX *)
        let v = List.map getVariables ols in
        let n_rules = calculate_new_rules_with_v_cond (Pair.snd condition1) true s0 pUpINV true v in
        look_for_new_rules k s0 p0 pUpINV n_rules linearCheck theorem upBound
       end
      else
       begin
        if theorem = 1 then
         (* Try to use improvements 2a and 2b *)
         improvement2a (Trs.to_list s0) p0 k >>= fun k1 ->
         improvement2b (Pair.snd condition1) s0 k1 >>= fun k2 ->
         if k2 = k or List.length (Trs.to_list k2) > upBound then
          Monad.return (false, Trs.empty, Trs.empty)
         else
          (* S can only have terminating rules, so eliminate non-terminating rules *)
          let el_nt = preprocessing (Trs.to_list k2) false in
          let other = List.diff (Trs.to_list k2) el_nt in
          let candidates = List.powerset other in
          let s1 = List.sort List.compare_length candidates in
          checkConfluence s1 k2 theorem upBound
        else
         (* if theorem = 2 or theorem = 3 *)
         (* CP(P U P^{-1},S) should be joinable - look for new rules *)
         let n_rules = calculate_new_rules (Pair.snd condition1) true s0 pUpINV false in
         look_for_new_rules k s0 p0 pUpINV n_rules linearCheck theorem upBound
       end
   end
  else
   (* P not reversible *)
   Monad.return (false, Trs.empty, Trs.empty)

 and look_for_new_rules k s0 p0 pUpINV n_rules linearCheck theorem upBound =
  (* Minimize new rules. New R = old R + added rules *)
  let new_R = minimize_new_rules (Trs.to_list n_rules) s0 in
  let impr_of_n_rules = improvement2 p0 new_R in
  if impr_of_n_rules <> [] then
   let k3 = minimize_with_improvement new_R s0 pUpINV impr_of_n_rules in
   let k2 = List.append (Trs.to_list k) (List.unique k3) in
   (* if new k is the same k as the old one stop. *)
   if Trs.of_list k2 = k or List.length k2 > upBound then
    Monad.return (false, Trs.empty, Trs.empty)
   else
    (* S can only have terminating rules, so eliminate non-terminating rules *)
    let el_nt = preprocessing k2 linearCheck in
    let other = List.diff k2 el_nt in
    let candidates = List.powerset other in
    let s1 = List.sort List.compare_length candidates in
    checkConfluence s1 (Trs.of_list k2) theorem upBound
  else
   Monad.return (false, Trs.empty, Trs.empty)

 and checkConfluence s k theorem upBound =
  if List.length (Trs.to_list k) >= upBound then
   Monad.return (false, Trs.empty, Trs.empty)
  else match s with
  | s0 :: s -> checkConfluence_inner s0 k theorem upBound >>= fun answer ->
    if Triple.fst answer then Monad.return answer else checkConfluence s k theorem upBound
  | [] -> Monad.return (false, Trs.empty, Trs.empty)
 ;;

 let startProof b p theorem =
  let new_S = Triple.snd b in
  let new_P = Triple.thd b in
  let q = P.make_sp (P.get_language p) (P.get_strategy p) new_S in
  Monad.return (if Triple.fst b then (Some (make p q new_P new_S (Trs.union new_S new_P) theorem))
                else None)
 ;;

 let confluenceProof p =
  let k = P.get_trs p in
  let klist = Trs.to_list k in
  (* eliminate non-terminating or non-left-linear rules (non-linear for Thm. 3) from S *)
  let el_nt = if !(flags.theorem) = 1 or !(flags.theorem) = 2 then preprocessing klist false
              else preprocessing klist true in
  let other = List.diff klist el_nt in
  let upBound = if (!(flags.bound) > 0 && !(flags.bound) < 19)  then !(flags.bound) else 12 in
  (* Avoid stack overflow *)
  if List.length other < 19 then
   if Trs.is_trs k then
    let candidates = List.powerset other in
    let s = List.sort List.compare_length candidates in
    checkConfluence s k !(flags.theorem) upBound >>= fun b ->
    startProof b p !(flags.theorem)
   else
    (* Failure: Not a TRS *)
    Monad.return None
  else
   (* Failure: Stack Overflow, too many list elements (2^19) *)
   Monad.return None
 ;;
end

let solve p =
 if P.is_crp p then
  AotoToyama.confluenceProof p
 else
  Monad.return None
;;

let solve fs p =
 let configure s = F.printf "%s@\n%!" s; flags.help := true in
 (try init (); Arg.parsex code spec fs with Arg.Bad s -> configure s);
 if !(flags.help) then (Arg.usage spec ("Options for "^code^":"); exit 0);
 solve p
;;
