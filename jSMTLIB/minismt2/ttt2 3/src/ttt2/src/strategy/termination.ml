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

(* Writing a wrapper for a processor:
 * There are two reasons why you have to write a wrapper for your processor.
 * On the on hand it must be guaranteed that each processor has the same
 * signature because otherwise they cannot be combined by the strategy. On
 * the other hand it is necessary to define the status of your processor and
 * its proof objects.
 * Writing a wrapper for your processor is quite easy. If the method [solve]
 * of your processor has a monadic return type you have to lift your processor
 * to the monad [M] by using the function [M.liftr]. Otherwise you can call
 * the method [solve] directly. After that change the current state according
 * to your processor proof object. Because each processor takes a single
 * problem as input and returns a list of new problems, the returned data must
 * have type [('a * S.t) list]. To lift results of this type to the monad [M]
 * use the function [M.result]. Finally you have to set the status of the new
 * termination problem. That means you have to specify if it is terminating,
 * nontermianting or open. If your processor failed you have to indicate that
 * by setting the status to fail. Note that you can automatically generate a
 * wrapper for your processor by using the function [M.execute] or
 * [M.executem] if your processor has a monadic return type.
 *
 * Register a new processor:
 * After you have written a wrapper for your processor, you have to register
 * it by editing the list [processor] below. Each entry has to be a tripple
 * consisting of the shortcut of the processor, the wrapper, and the help
 * messages. Important: To increase the readability of the wrapper file, the
 * name of the newly added wrapper should be identical to the shortcut you
 * have chosen for your method and registered by editing the list [processor].
 *)

(*** MODULES ******************************************************************)
module M = Monad;;
module P = Processor;;
module R = Processors.Rewritingx.Monad;;
module S = State;;

(*** OPENS ********************************************************************)
open Util;;
open Processors;;
open Rewritingx;;
open Termination;;
open Transformation;;

(*** MODULES ******************************************************************)
module Adg = Dg.Adg;;
module Cdg = Dg.Cdg;;
module Edg = Dg.Edg;;
module Tdg = Dg.Tdg;;
module SL = SemanticLabeling;;
module SC = SubtermCriterion;;
module SCT = SizeChangeTermination;;

module Fail = struct
 (*** TYPES *******************************************************************)
 type flags = {help : bool ref};;

 (*** GLOBALS *****************************************************************)
 let code = "fail";;
 let name = "Fail Processor";;
 let comment = "This processor always fails.";;
 let keywords = ["termination"];;
 let flags = {help = ref false};;

 let spec =
  let spec = [
   ("--help",Arg.Set flags.help,"Prints information about flags.");
   ("-help",Arg.Set flags.help,"Prints information about flags.");
   ("-h",Arg.Set flags.help,"Prints information about flags.")]
  in
  Arg.alignx 80 spec
 ;;

 let help = (comment,keywords,List.map Triple.drop_snd spec);;
end

module Sleep = struct
 (*** TYPES *******************************************************************)
 type flags = {help : bool ref; time : float ref};;

 (*** GLOBALS *****************************************************************)
 let code = "sleep";;
 let name = "Sleep Processor";;
 let keywords = ["termination"];;

 let comment =
  "This processor sleeps for a certain amount of time and fails afterwards."
 ;;

 let flags = {help = ref false; time = ref 0.0};;

 let spec =
  let spec = [
   ("--help",Arg.Set flags.help,"Prints information about flags.");
   ("-help",Arg.Set flags.help,"Prints information about flags.");
   ("-h",Arg.Set flags.help,"Prints information about flags.");
   ("-t",Arg.Set_float flags.time,
    "Specifies how many seconds the processor should sleep.")]
  in
  Arg.alignx 80 spec
 ;;

 let help = (comment,keywords,List.map Triple.drop_snd spec);;
end

module Succ = struct
 (*** TYPES *******************************************************************)
 type flags = {help : bool ref; no : bool ref};;

 (*** GLOBALS *****************************************************************)
 let code = "succ";;
 let name = "Success Processor";;
 let keywords = ["termination";"nontermination"];;
 let flags = {help = ref false; no = ref false};;

 let comment =
  "Defines a processor which, depending on the configuration, proves or \
   disproves termination. Note that this processor is not sound!"
 ;;

 let spec =
  let spec = [
   ("--help",Arg.Set flags.help,"Prints information about flags.");
   ("-help",Arg.Set flags.help,"Prints information about flags.");
   ("-h",Arg.Set flags.help,"Prints information about flags.");
   ("-no",Arg.Set flags.no,"States that the problem is nonterminating.")]
  in
  Arg.alignx 80 spec
 ;;

 let help = (comment,keywords,List.map Triple.drop_snd spec);;
end

(*** FUNCTIONS ****************************************************************)
let (>>=) = M.(>>=);;

(* let finished p = (Proof.make p [Proof.finished],Status.terminating);; *)
(* let unfinished p = (Proof.make p [Proof.unfinished],Status.unfinished);; *)
(* let failed = (Proof.unfinished,Status.fail);; *)

(* dependency pair processor *)
let dp fs _ = M.executem (Dp.solve fs) Dp.get_op (fun r -> P.P_dp r);;

(* processor which always fails *)
let fail fs _ =
 M.get >>= fun s ->
 (try Arg.parsex Fail.name Fail.spec fs with Arg.Bad s -> failwith s);
 let help = !(Fail.flags.Fail.help) in
 if help then (Arg.usage Fail.spec ("Options for "^Fail.name^":"); exit 0);
 M.return2 s (S.get_problem s) Proof.unfinished Status.fail
;;

(* arctic matrix method processor *)
let arctic fs _ =
 M.executem (Arctic.solve fs) Arctic.get_op (fun r -> P.P_arctic r)
;;

(* Bounds processor *)
let bounds fs _ =
 M.executem (Bounds.solve fs) Bounds.get_op (fun r -> P.P_bounds r)
;;

(* LPO processor *)
let lpo fs _ = M.executem (Lpo.solve fs) Lpo.get_op (fun r -> P.P_lpo r);;

(* KBO processor *)
let kbo fs _ = M.executem (Kbo.solve fs) Kbo.get_op (fun r -> P.P_kbo r);;
let tkbo fs _ = M.executem (Tkbo.solve fs) Tkbo.get_op (fun r -> P.P_tkbo r);;

(* matrix method processor *)
let matrix fs _ =
 M.executem (Matrix.solve fs) Matrix.get_op (fun r -> P.P_matrix r)
;;

(* ordinal interpretations *)
let ordinal fs _ =
 M.executem (Ordinal.solve fs) Ordinal.get_op (fun r -> P.P_ordinal r)
;;

(* higher ordinal interpretations *)
let epsilon0 fs _ =
 M.executem (EpsilonZero.solve fs) EpsilonZero.get_op (fun r -> P.P_eps0 r)
;;

(* fixed based elementary interpretations *)
let fbi fs _ =
 M.executem (Fbi.solve fs) Fbi.get_op (fun r -> P.P_fbi r)
;;


(* polynomial interpretations *)
let poly fs _ =
 M.executem (Poly.solve fs) Poly.get_op (fun r -> P.P_poly r)
;;

let cfs fs _ =
 M.executem (Cfs.solve fs) Cfs.get_op (fun r -> P.P_cfs r)
;;

(* SCC processor *)
let sccs fs _ = M.execute_list (Sccs.solve fs) Sccs.get_ops (fun r -> P.P_sccs r);;

(* size-change termination processor *)
let sct fs _ = M.executem (SCT.solve fs) SCT.get_op (fun r -> P.P_sct r);;

(* semantic labeling processor *)
let semantic_labeling fs _ =
 M.executem (SL.solve fs) SL.get_op (fun r -> P.P_sl r)
;;

(* simple projection subterm criterion processor *)
let sc fs _ = M.executem (SC.solve fs) SC.get_op (fun r -> P.P_sc r);;

(* processor which sleeps for a given time *)
let sleep fs _ =
 M.get >>= fun s ->
 (try Arg.parsex Sleep.name Sleep.spec fs with Arg.Bad s -> failwith s);
 let help = !(Sleep.flags.Sleep.help) in
 if help then (Arg.usage Sleep.spec ("Options for "^Sleep.name^":"); exit 0);
 let t = !(Sleep.flags.Sleep.time) in
 let ti = int_of_float (t +. 1.0) in
 ignore (Process.run_timed (Process.Local t) Unix.sleep ti);
 (* Unix.sleep !(Sleep.flags.Sleep.time); *)
 M.return2 s (S.get_problem s) Proof.unfinished Status.fail
;;

(* processor which always succeeds *)
let succ fs _ =
 M.get >>= fun s ->
 (try Arg.parsex Succ.name Succ.spec fs with Arg.Bad s -> failwith s);
 let help = !(Succ.flags.Succ.help) and no = !(Succ.flags.Succ.no) in
 if help then (Arg.usage Succ.spec ("Options for "^Succ.name^":"); exit 0);
 let status = if no then Status.nonterminating else Status.terminating in
 M.return2 s (S.get_problem s) Proof.finished status
;;

let trivial fs _ =
  M.executem (Trivial.solve fs) Trivial.get_op (fun r -> P.P_trivial r);;

(* ADG processor *)
let adg fs _ = M.executem (Adg.solve fs) Adg.get_op (fun r -> P.P_adg r);;

(* CDG processor *)
let cdg fs _ = M.executem (Cdg.solve fs) Cdg.get_op (fun r -> P.P_cdg r);;

(* EDG processor *)
let edg fs _ = M.executem (Edg.solve fs) Edg.get_op (fun r -> P.P_edg r);;

(* TDG processor *)
let tdg fs _ = M.executem (Tdg.solve fs) Tdg.get_op (fun r -> P.P_tdg r);;


(* FIXME delete processor confluence *)
let rulelabeling fs _ =
 M.executem (Confluence.RuleLabeling.solve fs) Confluence.RuleLabeling.get_op (fun r -> P.P_rl r)
;;

let shift fs _ =
 M.executem (Confluence.Shift.solve fs) Confluence.Shift.get_op (fun r -> P.P_shift r)
;;

let decreasing fs _ =
 M.executem (Confluence.Decreasing.solve fs) Confluence.Decreasing.get_op (fun r -> P.P_dec r)
;;

let groundcr fs _ =
 M.executem_result (Confluence.GroundCR.solve fs) Confluence.GroundCR.get_result (fun r -> P.P_groundcr r)
(* FIXME delete processor confluence *)


(*** GLOBALS ******************************************************************)
let processors = [
 (Adg.code,adg,Adg.help);
 (Arctic.code,arctic,Arctic.help);
 (Bounds.code,bounds,Bounds.help);
 (Cdg.code,cdg,Cdg.help);
 (Cfs.code,cfs,Cfs.help); 
 (Dp.code,dp,Dp.help);
 (Edg.code,edg,Edg.help);
 (EpsilonZero.code,epsilon0,EpsilonZero.help);
 (Fbi.code,fbi,Fbi.help);
 (Fail.code,fail,Fail.help);
 (Kbo.code,kbo,Kbo.help);
 (Tkbo.code,tkbo,Tkbo.help);
 (Lpo.code,lpo,Lpo.help);
 (Matrix.code,matrix,Matrix.help);
 (Ordinal.code,ordinal,Ordinal.help);
 (Poly.code,poly,Poly.help);
 (SC.code,sc,SC.help);
 (Sccs.code,sccs,Sccs.help);
 (SCT.code,sct,SCT.help);
 (SL.code,semantic_labeling,SL.help);
 (Sleep.code,sleep,Sleep.help);
 (Succ.code,succ,Succ.help);
 (Tdg.code,tdg,Tdg.help);
 (Trivial.code,trivial,Trivial.help);
(* FIXME delete processor confluence *)
 (Confluence.RuleLabeling.code,rulelabeling,Confluence.RuleLabeling.help);
 (Confluence.Shift.code,shift,Confluence.Shift.help);
 (Confluence.Decreasing.code,decreasing,Confluence.Decreasing.help);
 (Confluence.GroundCR.code,groundcr,Confluence.GroundCR.help);
(* FIXME delete processor confluence *)
 (* (Sorted.code,sorted,Sorted.help); *)
];;
