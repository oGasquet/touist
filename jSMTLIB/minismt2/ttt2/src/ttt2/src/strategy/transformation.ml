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
open Transformation;;

(*** MODULES (part 2) *********************************************************)
module RLab = RootLabeling;;
module QLab = QuasiRootLabeling;;
module Ti   = TypeIntroduction;;

(*** FUNCTIONS ****************************************************************)
let (>>=) = M.(>>=);;

(*
let finished p = (Proof.make p [Proof.finished],Status.terminating);;
let unfinished p = (Proof.make p [Proof.unfinished],Status.unfinished);;
let failed = (Proof.unfinished,Status.fail);;
*)

(* commmutativiy transformation *)
let commute fs _ = M.executem (Commute.solve fs) Commute.get_op (fun r -> P.P_co r);;

(* complexity transformation *)
let cp fs _ = M.executem (Cp.solve fs) Cp.get_op (fun r -> P.P_cp r);;

(* linearization *)
let linear fs _ =
 M.executem (Linear.solve fs) Linear.get_op (fun r -> P.P_linear r)
;;

(* quasi root-labeling transformation *)
let qlab fs _ = M.executem (QLab.solve fs) QLab.get_op (fun r -> P.P_qlab r);;

(* reflect transformation *)
let ref fs _ =
 M.executem (Reflect.solve fs) Reflect.get_op (fun r -> P.P_ref r)
;;

(* reverse transformation *)
let rev fs _ =
 M.executem (Reverse.solve fs) Reverse.get_op (fun r -> P.P_rev r)
;;

(* root-labeling transformation *)
let rlab fs _ = M.executem (RLab.solve fs) RLab.get_op (fun r -> P.P_rlab r);;

(* relative termination transformation *)
let rt fs _ = M.executem (Rt.solve fs) Rt.get_op (fun r -> P.P_rt r);;

(* dpify transformation *)
let dpify fs _ = M.executem (Dpify.solve fs) Dpify.get_op (fun r -> P.P_dpify r);;

(* emb transformation *)
let emb fs _ = M.executem (Emb.solve fs) Emb.get_op (fun r -> P.P_emb r);;

(* closedness transformation *)
let closed fs _ = M.executem (Confluence.Closed.solve fs) Confluence.Closed.get_op (fun r -> P.P_cl r);;

(* Aoto-Toyama criterion (transformation) *)
let aotoToyama fs _ = M.executem (Confluence.AotoToyama.solve fs) Confluence.AotoToyama.get_op (fun r -> P.P_aotoToyama r);;

(* Klein-Hirokawa criterion (transformation) *)
let kleinHirokawa fs _ = M.executem (Confluence.KleinHirokawa.solve fs) Confluence.KleinHirokawa.get_op (fun r -> P.P_kleinHirokawa r);;

(* church rosser transformation *)
let cr fs _ = M.executem (Cr.solve fs) Cr.get_op (fun r -> P.P_cr r);;

(* sortedness transformation *)
let sorted fs _ = M.executem_list (Sorted.solve fs) Sorted.get_ops (fun r -> P.P_sorted r);;

(* split transformation *)
let split fs _ = M.execute_list (Split.solve fs) Split.get_ops (fun r -> P.P_split r);;

(* standard termination transformation *)
let st fs _ = M.executem (St.solve fs) St.get_op (fun r -> P.P_st r);;

(* type introduction transformation *)
let ti fs _ = M.executem_list (Ti.solve fs) Ti.get_ops (fun r -> P.P_ti r);;

(* uncurrying processor *)
let uncurry fs _ =
 M.executem (Uncurry.solve fs) Uncurry.get_op (fun r -> P.P_uncurry r)
;;

(* extended uncurrying processor *)
let uncurryx fs _ =
 M.executem (Uncurryx.solve fs) Uncurryx.get_op (fun r -> P.P_uncurryx r)
;;

(* usable rules processor *)
let ur fs _ = M.executem (Ur.solve fs) Ur.get_op (fun r -> P.P_ur r);;

(*** GLOBALS ******************************************************************)
let processors = [
 (Cp.code,cp,Cp.help);
 (Dpify.code,dpify,Dpify.help);
 (Emb.code,emb,Emb.help);
 (Linear.code,linear,Linear.help);
 (QLab.code,qlab,QLab.help);
 (Reflect.code,ref,Reflect.help);
 (Reverse.code,rev,Reverse.help);
 (RLab.code,rlab,RLab.help);
 (Rt.code,rt,Rt.help);
 (Sorted.code,sorted,Sorted.help);
 (Split.code,split,Split.help);
 (St.code,st,St.help);
 (Ti.code,ti,Ti.help);
 (Uncurry.code,uncurry,Uncurry.help);
 (Uncurryx.code,uncurryx,Uncurryx.help);
 (Ur.code,ur,Ur.help);
 (*confluence*)
 (Cr.code,cr,Cr.help);
 (Confluence.Closed.code,closed,Confluence.Closed.help);
 (Confluence.AotoToyama.code,aotoToyama,Confluence.AotoToyama.help);
 (Confluence.KleinHirokawa.code,kleinHirokawa,Confluence.KleinHirokawa.help);
 (Commute.code,commute,Commute.help);
 ("add",commute,Commute.help);
];;
