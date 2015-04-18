(* $Id: main.ml,v 1.100 2013/10/28 07:45:30 hzankl Exp $ *)

(* Copyright 2009 Harald Zankl
 * GNU Lesser General Public License
 *
 * This file is part of MiniSMT.
 * 
 * MiniSMT is free software: you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or (at your
 * option) any later version.
 * 
 * MiniSMT is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public
 * License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with MiniSMT. If not, see <http://www.gnu.org/licenses/>.
 *)
(*TODO:
 - do not unfold let flet
 - n-ary ``-'' is dangerous (what is the semantics?)
 - timeout and error (what is when)
*)

(*** OPENS ********************************************************************)
open Util;;

(*** MODULES ******************************************************************)
module L = Logic;;
module B = Bv;;

(*** EXCEPTIONS ***************************************************************)
exception Help;;
exception Version;;

(*** TYPES ********************************************************************)
type assignment = ((string * L.Number.t) list * (string * bool) list);;
type back = SmtFormula.back = UNKNOWN | UNSAT | SAT of assignment;;
type answer = YES | NO | MAYBE | TIMEOUT;;
type flags = {
 answer   : bool ref;   (*print answer*)
 bv       : bool ref;   (*use bitvector backend*)
 bvold    : bool ref;   (*use old bitvector backend*)
 comp     : bool ref;   (*competition strategy (qf_nia) *)
 file     : string ref; (*input file*)
 db       : int ref ;   (*bits after decimal point (for helper variables)*)
 ib       : int ref;    (*upper bound for arithmetic variables (in bits)*)
 ob       : int ref;    (*upper bound for helper variables (in bits)*)
 model    : bool ref;   (*print model*)
 neg      : bool ref;   (*allow negative numbers*)
 pb       : bool ref;   (* translate to pseudo-boolean *)
 pbsolver : string ref; (* script used to translate PB to SAT *)
 pboptions: string ref; (* options for running gpw internally *)
 rat      : int ref;    (*denominator for arithmetic variables*)
 real     : bool ref;   (*allow real numbers*)
 s        : bool ref;   (*solve*)
 simp     : int  ref;   (*simplify formula*)
 smt      : bool ref;   (*output file in SMT-LIB format*)
 stdin    : bool ref;   (*read from STDIN*)
 timeout  : float ref;  (*time allowed for solving*)
 twostep  : bool ref;   (*dis/allow two step solving process*)
 smtlib   : bool ref;   (*parse SMT-LIB format 1.0 or 2.0*)
 (*TMP*)
 minisatp : bool ref; (* use smt2pb with minisat+ *)
 nlsol    : bool ref;
 stopwatch: bool ref;
 yesno    : bool ref;
};;

let flags = {
 answer   = ref true;
 bv       = ref false;
 bvold    = ref false;
 comp     = ref false;
 file     = ref "";
 db       = ref 1;
 (* ib       = ref 5; *)
 (* ob       = ref 10; *)
 ib = ref ~-1;
 ob = ref ~-1;
 model    = ref false;
 neg      = ref true;
 pb       = ref false;
 pbsolver = ref "";
 pboptions= ref "";
 rat      = ref 2;
 real     = ref false;
 s        = ref true;
 simp     = ref 0;
 smt      = ref false;
 stdin    = ref false;
 timeout  = ref 0.0;
 twostep  = ref true;
 smtlib   = ref true;
 (*TMP*)
 minisatp = ref false;
 nlsol = ref false;
 stopwatch = ref true;
 yesno = ref false;
};;

(*** GLOBALS ******************************************************************)
let usage = Format.sprintf "Usage: %s [flags] [file]" (Sys.argv.(0));;
let version = "0.6";;

(*** FUNCTIONS ****************************************************************)

let help = [
 ("-h", Arg.Unit (fun () -> raise Help), "print this help message");
 ("--help", Arg.Unit (fun () -> raise Help), "print this help message");
 ("-", Arg.Set flags.stdin, "read from stdin (default off)");
 ("-a", Arg.Clear flags.answer, "print answer (default on)");
 ("-backend", Arg.String SmtFormula.set_solver,
  "set the backend SAT-solver (default MiniSat)");
 ("-bv", Arg.Set flags.bv, "use bitvector backend (default off)");
 ("-comp", Arg.Unit (fun _ -> flags.comp := true;
   SmtFormula.infer := true; SmtFormula.set_comp_solver ()),
  "use competition mode (qf_nia, default off)");
 ("-d", Arg.Set Debug.on, "give debug output (default off)");
 ("-db", Arg.Set_int flags.db, "bits after decimal point (default 1)");
 ("-ib", Arg.Set_int flags.ib, "arithmetical variables (in bits, default: heuristic)");
 ("-infer", Arg.Set SmtFormula.infer, "infer lower/upper bounds (default: off)");
 ("-ob", Arg.Set_int flags.ob, "helper variables (in bits, default: heuristic)");
 ("-m", Arg.Set flags.model, "print model (default off)");
 ("-neg", Arg.Clear flags.neg, "allow negative numbers (default on)");
 ("-pb", Arg.Set flags.pb, "translate to pseudo-boolean constraints (default off)");
 ("-pb.bdd", Arg.Set_int Pb2bdd.bdd, "choose bdd generation; 0 unreduced, 1 reduced, 2 w/o duplicated variables (default 1)");
 ("-pb.dv", Arg.Unit (fun _ -> Pb2bdd.dv := true;),
    "pb: drop same variables along a path in BDD)");
 ("-pb.order", Arg.Unit (fun _ -> Pb2bdd.var_order := Pb2bdd.INC;),
    "pb: set increasing variable order (default:decreasing)");
 ("-pb.po2", Arg.Unit (fun _ -> Pb2bdd.po2 := true;),
    "pb: decompose to power-of-two constraint)");
 ("-po", Arg.Set_string flags.pboptions, "options for pseudo-boolean solver (default: none)");
 ("-ps", Arg.Set_string flags.pbsolver, "pseudo-boolean solver (default: internal)");
 ("-rat", Arg.Set_int flags.rat, "denominator (default 2)");
 ("-real", Arg.Set flags.real, "force real numbers (default off)");
 ("-refine_ib", Arg.String (SmtFormula.set_refine_bits SmtFormula.refine_ib),
  "set how to refine ib if unsat (default *2, +n or *n allowed)");
 ("-refine_ob", Arg.String (SmtFormula.set_refine_bits SmtFormula.refine_ob),
  "set how to refine ob if unsat (default +2, +n or *n allowed)");
 ("-s", Arg.Clear flags.s, "solve (default on)");
 ("-smt", Arg.Set flags.smt, "output problem in smt-lib format");
 ("-t", Arg.Set_float flags.timeout, "set timeout (standard: infinity)");
 ("-twostep", Arg.Clear flags.twostep, "disable two step solving process (default enabled)");
 ("-v", Arg.Unit (fun () -> raise Version), "print version and exit");
 ("-v1", Arg.Clear flags.smtlib, "parse SMT-LIB v1.0 format");
 ("-v2", Arg.Set   flags.smtlib, "parse SMT-LIB v2.0 format (standard)");
 (*TMP*)
 ("-minisatp", Arg.Set flags.minisatp, "tmp: smt2pb with input from minisat+");
 ("-nlsol", Arg.Set flags.nlsol, "tmp:output for nlsol");
 ("-bvcache", Arg.Clear B.bvcache, "tmp:use caching for bitvectors (default on)");
 ("-bvi", Arg.Clear B.bvi, "tmp:use interfaced bitvector backend (default on)");
 ("-simp", Arg.Set_int flags.simp, "tmp:simplify problem before solving [0,1,2]");
 ("-yesno", Arg.Set flags.yesno, "tmp:output yes/no instead of sat/unsat");
];;

let help = Arg.alignx 80 help;;

let configure () = 
 Arg.parse help (fun x -> flags.file := x) usage;
 flags
;;

let ffile file = 
 let max = min (String.length file) 15 in
 let l = String.sub file (String.length file - max) max in
 if l = file then file else ".." ^ l
;;

let answertostring yesno a = 
 if yesno then match a with
   | YES -> "YES"
   | NO -> "NO"
   | MAYBE -> "MAYBE"
   | TIMEOUT -> "UNUSUAL TERMINATION"
  else match a with
   | YES -> "sat"
   | NO -> "unsat"
   | MAYBE -> "unknown"
   | TIMEOUT -> "unusual termination"
;;

let print_answer b yesno a = if b then 
 Format.printf "%s@\n" (answertostring yesno a);;

let print_time b t = if b then
 Format.printf "%.2f@\n" t;;

let print_model b = function
 | None -> ()
 | Some (al,xl) -> if b then (
  List.iter (fun (a,va) -> Format.printf "%s = %a@\n" a L.Number.fprintf va) al;
  List.iter (fun (x,vx) -> Format.printf "%s = %b@\n" x vx) xl;
 );;

let two_step solve ipt =
 let solve = solve !(flags.ib) !(flags.ob) !(flags.rat) !(flags.db) !(flags.real) in
 let solves = match !(flags.twostep), !(flags.neg) with
   | true, false -> [solve false]
   | true, true  -> [solve false; solve true]
   | false, neg  -> [solve neg] in
 let rec solve_all = function
   | [] -> UNKNOWN
   | s::ss -> (match s ipt with | UNKNOWN -> solve_all ss | x -> x) in
 solve_all solves
;;

(*bitvector subtraction is not defined for nats*)
let wrap f ipt = try f ipt with _ -> UNKNOWN;;

let comp_nia solve ipt = 
 let solve ib ob = solve ib ob !(flags.rat) !(flags.db) !(flags.real) in
 let fs = if !(flags.bv) then [wrap (solve 3 4 false); solve 3 4 true; solve 33 50 true]
  else [solve 3 4 false; solve 3 4 true; solve 33 50 false; solve 33 50 true] in
 match Process.run_parallel_until ((<>) UNKNOWN) fs ipt with
  | None -> UNKNOWN
  | Some x -> x
;;

let comp_nra solve ipt = 
 let solve ib ob = solve ib ob !(flags.rat) !(flags.db) !(flags.real) in
 let fs = [
  solve 2 2 false;
  solve 2 6 false;
  solve 3 2 false;
  solve 3 6 false;
  solve 4 6 false;
 ] in
 match Process.run_parallel_until ((<>) UNKNOWN) fs ipt with
  | None -> UNKNOWN
  | Some x -> x
;;

let comp solve ipt = 
 let s = match ipt.SmtFormula.logic with
  | "QF_NRA" -> comp_nra
  | _ -> comp_nia
 in
 s solve ipt
;;

let h_ib x = ((x+100)*(x+100))/((x+10)*(x+10)) + 1;;
let h_ob x = ((x+200)*(x+200))/((x+20)*(x+20)) + 1;;

let h_ib m v l = match (m,v) with
 | m,v when m < 34 && v < 51 && l -> 33
 | m,_ when m < 200 -> 4
 | m,_ when m < 2_000 -> 3
 | m,_ when m < 5_000 -> 2
 | _ -> 1
;;

let h_ob m v l = match (m,v) with
 | m,v when m < 34 && v < 51 && l -> 50
 | m,_ when m < 200 -> 5
 | m,_ when m < 2_000-> 4
 | m,_ when m < 5_000 -> 3
 | _ -> 2
;;
 
let h_real m v l = match (m,v) with
 | (m,v) when m < 10 && v < 10 -> true
 | _ -> false
;;

let nra ipt = ipt.SmtFormula.logic = "QF_NRA";;

let heuristic ipt = 
 let f = SmtFormula.And (ipt.SmtFormula.assumptions @ [ipt.SmtFormula.formula]) in
 let m = SmtFormula.count_mul f in
 let v = List.length (ipt.SmtFormula.extrafuns) in
 let l = SmtFormula.count_large_const f > 0 in
 Debug.debug (Format.sprintf "#mul = %d, #var = %d" m v);
 if !(flags.ib) < 0 then (
  flags.ib := h_ib m v l; 
  Debug.debug (Format.sprintf "heuristic: ib = %d" !(flags.ib))
 );
 if !(flags.ob) < 0 then (
  flags.ob := h_ob m v l;
  Debug.debug (Format.sprintf "heuristic: ob = %d" !(flags.ob))
 );
 flags.real := (!(flags.real) || h_real m v l) && nra ipt ; 
 Debug.debug (Format.sprintf "heuristic: real = %b" !(flags.real));
 flags.rat := if nra ipt then !(flags.rat) else 1; 
 Debug.debug (Format.sprintf "heuristic: rat = %d" !(flags.rat));
;;

let rec loop f x n = if n <= 0 then x else loop f (f x) (n-1);;

(*read smt2 format from stdin*)
let select_parser file = 
 let suffix = if !(flags.smtlib) then "smt2" else "smt" in (*standard v2.0*)
 let suffix = try Filename.extension file with | Not_found -> suffix in
 if suffix = "smt" then
  Parser.parse Lexer.token
 else if suffix = "smt2" then
  Parser2.parse Lexer2.token
 else
  failwith (Format.sprintf "unknown file extension: %s" suffix)
;;

let run flags =
 let parse = select_parser !(flags.file) in
 let cin = if !(flags.stdin) || !(flags.file) = "" then stdin else open_in !(flags.file) in
 let lexbuf = Lexing.from_channel cin in
 let ipt = parse lexbuf in
 Debug.debug ("file " ^ (ffile !(flags.file)) ^ " parsed"); 
 if !(flags.pb) then
  Smt2pbc.solve !(flags.ib) !(flags.db) !(flags.ob) !(flags.pbsolver) !(flags.pboptions) ipt
 else (
 (* let ipt = SmtFormula.unfold_eq ipt in *)
 let _ = heuristic ipt in 
 let ipt = SmtFormula.unfold ipt in
(* simplify formula and check for unsatisfiability *)
 (* let ipt = SmtFormula.learn_nn ipt in *)
(**)
 let ipt = loop SmtFormula.simplify ipt !(flags.simp) in
(**)

 if !(flags.smt) then
  Format.printf "@[%a@]\n%!" SmtFormula.fprintf ipt;
 if !(flags.nlsol) then
  Format.printf "@[%a@]\n%!" SmtFormula.fprintf_nlsol2 ipt;
 if not !(flags.s) then exit 0;
 let solve ib ob rat db real neg ipt = if !(flags.bv) then
  (match Bitvector.solve ib ob rat db real neg ipt with
  | Some ass -> SAT ass | _ -> UNKNOWN)
  else SmtFormula.solve ib ob rat db real neg ipt in
 let r = 
  if !(flags.comp) then comp solve ipt 
  else two_step solve ipt
 in
 Debug.debug "formula solved"; 
 let a = match r with 
  | SAT ass -> SAT ass
  | UNSAT -> UNSAT
  | _ when List.mem SmtFormula.bot ipt.SmtFormula.assumptions -> UNSAT
  | _ -> UNKNOWN
 in 
 a
 ) (* end non-pb *)
;;

let main () =
 try
  (* read from stdin if no arguments specified *)
  (* if Array.length Sys.argv = 1 then raise Help; *)
  let flags = configure () in
  let start = Unix.gettimeofday () in 
  let a = 
   if !(flags.timeout) > 0.0 then
    let t = Process.Local !(flags.timeout) in
    let (a,t) = Process.run_timed t run flags in
    a
   else 
    Some (run flags)
  in
  let t = Unix.gettimeofday () -. start in
  let (answer,model) = match a with 
   | None -> (TIMEOUT, None)
   | Some UNSAT -> (NO,None)
   | Some SAT ass -> (YES,Some ass)
   | Some UNKNOWN -> (MAYBE,None)
  in 
  print_answer !(flags.answer) !(flags.yesno) answer;
  print_time !(flags.stopwatch) t;
  print_model  !(flags.model)  model;
  Format.printf "%!";
  with 
   | Help -> Arg.usagex Format.std_formatter help usage;
   | Failure "lexing: empty token" -> Format.printf "lexing error@\n";
   | Parsing.Parse_error -> Format.printf "parse error@\n";
   | Version -> Format.printf "%s@\n" version;
;;

(* try *)
 main ()
(* with _ -> Format.printf "Unusual termination@\n%!";; *)
