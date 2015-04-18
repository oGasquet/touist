(* Copyright 2011 Simon Legner, Christian Sternagel, Harald Zankl
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
open Monad;;
open Formula;;
open Util;;

(*** MODULES ******************************************************************)
module Idx = Index.Standard (Int);;
module PS = PicosatInterface;;

(*** FUNCTIONS ****************************************************************)

let debug description debugfun =
 let fmt = Format.std_formatter in
 let _ = Format.print_flush () in
 let _ = Printf.printf "\n%s\n" description in
 let _ = debugfun fmt in
 let _ = Format.print_newline () in
 ()
;;

(*temporary*)
let index x idx = 
 ignore (Idx.index x idx);
 Idx.find_key x idx
;;

exception Literal_superfluent
exception Disjunct_superfluent
let rec lit2int vars = function
 | Bot | Not Top -> raise Literal_superfluent
 | Top | Not Bot -> raise Disjunct_superfluent
 | P x           -> (index x vars) + 1
 | Not (Not l)   -> lit2int vars l 
 | Not l         -> let i = lit2int vars l in (-1) * i
 | _             -> (* non-literal formula in lit2int *) 
  raise (Match_failure ("PLog.lit2int", 0, 0))
;;

let to_dimacs clause vars = 
 let rec to_dimacs res vars = function
  | []    -> res
  | l::ls ->
   try to_dimacs (lit2int vars l::res) vars ls with
    | Literal_superfluent  -> to_dimacs res vars ls
    | Disjunct_superfluent -> [0] (* 0 = unused index *)
 in
 to_dimacs [] vars clause
;;
(*temporary*)

let send_dimacs cnf idx =
 let send_clause = function
  | [0] -> None
  | xs ->
    let _ = List.iter (ignore <.> PS.picosat_add) xs in
    let _ = PS.picosat_add 0 in
    Some xs
 in
 List.map_option (send_clause <.> (flip to_dimacs idx)) cnf
;;

let cnf_to_pred idx =
 (flip Idx.find_elt idx) <.> (flip (-) 1) <.> abs
;;

let solve_aux cnf =
 let (>>?=) v f = match v with Some x -> f x | None -> return (Left None) in
 let idx = Idx.empty 512 in
 let _ = PS.picosat_init () in
 let _ = PS.picosat_enable_trace_generation () in
 let clauses = send_dimacs cnf idx in
 match PS.picosat_sat (-1) with
  | 10 (* SAT *) ->
    let assign = Idx.fold (fun x_raw x_internal ass ->
     let x_cnf = x_raw + 1 in
     let tf = if PS.picosat_deref x_cnf > 0 then true else false in
     Assignment.add_p (P x_internal) tf ass
     ) Assignment.empty idx in
    let _ = debug "assignment" (fun f -> Assignment.fprintf f assign) in
    let _ = PS.picosat_reset () in
    return (Right assign)
  | 20 (* UNSAT *) ->
    let all_core = List.filteri (fun i x -> PS.picosat_coreclause i) clauses in
    let _ = debug "PicoSat core" (fun ppf ->
     List.fprintf (List.fprintf Int.fprintf " ") "\n" ppf all_core) in
    let core_singleton = Hashtbl.create 512 in
    let _ = List.iteri (fun i -> function
     | [x] ->
       (if PS.picosat_coreclause i then
        Hashtbl.add core_singleton (P (cnf_to_pred idx x)) ())
     | _ -> ()) clauses in
    get >>= fun s ->
    let core_frm = Hashtbl.fold (fun frm pred acc ->
     if Hashtbl.mem core_singleton pred then frm::acc else acc)
     (fst s.State.tt_tbl)
     (Hashtbl.fold (fun x _ acc -> x::acc) core_singleton []) in
    let core_frm_p = List.unique (List.flat_map Formula.p_props core_frm) in
    let core_a_overapprox = Hashtbl.fold (fun cnf minf accu ->
     let is_in_core p = List.mem p core_frm_p in
     if List.exists is_in_core (BinType.to_list minf) then
      cnf::accu else accu) s.State.ta_tbl [] in
    let overflow_constraints_vars = List.flat_map Formula.p_props
     (Hashtbl.domain s.State.overflow_constraints) in
    let is_overflow_in_core = not (
     List.is_empty (List.intersect overflow_constraints_vars core_frm_p)) in
    let _ = debug "formulas in core (i.e. fst tt_tbl)" (fun ppf ->
     List.fprintf Formula.fprintf_p "\n" ppf core_frm) in
    let _ = debug "propositional variables in core (i.e. fst tt_tbl)" (fun ppf ->
     List.fprintf Formula.fprintf_p " " ppf core_frm_p) in
    let _ = debug "propositional variables in overflow constraints" (fun ppf ->
     List.fprintf Formula.fprintf_p " " ppf overflow_constraints_vars) in
    let unit_formatter ppf () = Format.fprintf ppf "" in
    let _ = debug "contents of ta_tbl" (fun ppf ->
     Hashtbl.fprintf ~delim:": "
     Formula.fprintf_a BinMinf.fprintf ppf s.State.ta_tbl) in
    let _ = debug "contents of sc (side conditions)" (fun ppf ->
     Hashtbl.fprintf ~delim:""
     Formula.fprintf_p unit_formatter ppf s.State.sc) in
    let _ = debug "contents of overflow constraints" (fun ppf ->
     Hashtbl.fprintf ~delim:""
     Formula.fprintf_p unit_formatter ppf s.State.overflow_constraints) in
    let _ = PS.picosat_reset () in
    let debug_fun ?fprintf_a:(fprintf_a=Formula.fprintf_a) ppf =
     Hashtbl.fprintf ~delim:" = " fprintf_a
     (BinMinf.fprintfh (flip List.mem core_frm_p)) ppf s.State.ta_tbl in
    return (Left (Some (core_a_overapprox, is_overflow_in_core, debug_fun)))
;;

let solve_cnf cnf = 
  MiniSat.shape_cnf cnf >>= fun cnf ->
  solve_aux cnf
;;

let solve f =
  MiniSat.to_cnf f >>= fun cnf ->
  solve_cnf cnf 
;;
