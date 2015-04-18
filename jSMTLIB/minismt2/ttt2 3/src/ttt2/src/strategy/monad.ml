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
open Processors;;

(*** MODULES ******************************************************************)
module R = Rewritingx.Monad
module S = State;;

(*** TYPES ********************************************************************)
type state = S.t;;

(* TTT2 Strategy core.
 *
 * The computation proceeds in stages (separated by ; in the strategy language),
 * which essentially consist of a list of subproblems. Subproblems can be in
 * four states (see Status module), indicating failure, termination,
 * nontermination, or an unfinished problem. All subproblems of a stage have
 * to be shown terminating in order to conclude termination.
 *
 * Each time a processor is run, it is applied to all the currently unfinished
 * subproblems in sequence, producing a new list of subproblems for the next
 * stage.
 *
 * As an optimization, if nontermination is detected, processing is stopped;
 * if fail_early (strategy language: s%) is enabled, this is also done for
 * failures.
 *
 * This actually fails to be a monad except on a very coarse but highly
 * important level: if the only observable of the strategy core were the answer
 * (yes / no / maybe / open), then the monad laws hold, as long as the
 * fail_early feature is not used; with fail_early, we may get 'maybe' answers
 * instead of 'no' answers.
 *)
module Stage = struct
 (*** TYPES ******************************************************************)
 type 'a problem = Todo of 'a * state | Done of state;;
 type 'a t = { fail_early : bool; problems : 'a problem list };;

 (*** FUNCTIONS **************************************************************)
 let make fl a s = { fail_early = fl; problems = [Todo (a, s)] };;
 let makes fl xs =
   { fail_early = fl; problems = List.map (fun (a,s) -> Todo (a, s)) xs };;

 let set_fail_early st fl = { st with fail_early = fl };;

 let get_problem_state = function Todo (_, s) -> s | Done s -> s;;
 let mark_problem_done p = Done (get_problem_state p);;
 let get_states st = List.map get_problem_state st.problems;;

 (* find combined status of stage, as the conjunction of the current states *)
 let status st = List.foldl1 Status.collect
   (List.map (State.get_status <.> get_problem_state) st.problems);;

 (* Compute next stage: Apply the function f : 'a -> state -> bool -> 'b t R.t
  * to all unfinished Todo problems, with some shortcut evaluation. *)
 let unfold st f =
  let (>>=) = R.(>>=) in
  let check_shortcut st =
   let s = status st in
   Status.is_nonterminating s || st.fail_early && Status.is_fail s in
  if check_shortcut st then
   R.return { st with problems = List.map mark_problem_done st.problems }
  else
   let rec go fl acc = function
    | [] -> R.return { fail_early = fl; problems = List.rev acc }
    | Done s :: xs -> go fl (Done s :: acc) xs
    | Todo (a, s) :: xs ->
     let status = State.get_status s in
     if not (Status.is_unfinished (State.get_status s)) then
      go fl (Done s :: acc) xs
     else
      R.(>>=) (f a s fl) (fun st' ->
       if check_shortcut st' then
        R.return
         { st' with problems =
           List.rev_append (List.rev_append st'.problems acc)
            (List.map mark_problem_done xs) }
       else
        go st'.fail_early (List.rev_append st'.problems acc) xs)
   in go st.fail_early [] st.problems;;
end

(*** INCLUDES *****************************************************************)
include Monad.Make (struct
 type 'a t = state -> bool -> 'a Stage.t R.t;;
 let return x = fun s fl -> R.return (Stage.make fl x s);;
 let (>>=) m f = fun s fl -> R.(>>=) (m s fl) (fun st -> Stage.unfold st f);;
end)

(*** FUNCTIONS ****************************************************************)
(* Monadic Functions *)
let get = fun s fl -> R.return (Stage.make fl s s);;

let execute s fl s' m =
 let (st, s') = either failwith id (R.eval s' (m s fl)) in
 (st, s', Stage.status st)
;;

let run s s' m =
 let filter = Proof.merge <.> List.map State.get_proof <.> Stage.get_states in
 let error = Format.sprintf "error '%s' occurred" in
 try Triple.apply filter id id (execute s false s' m)
 with Failure s -> failwith (error s)
;;

(* Constructors *)
let lift m = fun s fl -> R.(>>=) m (fun a -> R.return (Stage.make fl a s));;
let result xs = fun _ fl -> R.return (Stage.makes fl xs);;

(* Combinators *)
(* s ; s *)
let combine = (>=>);;

(* s | s *)
let choose f g x = fun s fl ->
 R.(>>=) (f x s fl) (fun st ->
  if Status.is_fail (Stage.status st) then g x s fl else R.return st)
;;

(* s || s *)
let parallel f g x = fun s fl ->
 R.(>>=) R.get (fun s' ->
 let is_success = Status.is_success <.> Triple.thd in
 let f = execute s fl s' <.> f and g = execute s fl s' <.> g in
 match Process.run_parallel_until is_success [f;g] x with
  | None -> result [(x,State.set_status Status.fail s)] s fl
  | Some (xs,s',_) -> R.(>>) (R.set s') (R.return xs))
;;

(* if p then s else s *)
let condition = ite;;

(* {s}s *)
let alter f g x = get >>= fun s -> f x >>= g (State.get_problem s);;

(* Iterators *)
let reapply f st = (fun s fl -> R.return st) >>= f;;

(* s? *)
let optional f x = fun s fl ->
 R.(>>=) (f x s fl) (fun st ->
 if Status.is_fail (Stage.status st) then result [(x,s)] s fl else R.return st)
;;

(* s* *)
let rec iterate f x = fun s fl ->
 R.(>>=) (f x s fl) (fun st ->
 if Status.is_fail (Stage.status st) then result [(x,s)] s fl else
   reapply (iterate f) st s fl)
;;

(* s+ *)
let rec repeat f x = f x >>= repeat f;;

(* sn* *)
let rec duplicate n f x = fun s fl ->
 R.(>>=) (f x s fl) (fun st ->
 if Status.is_fail (Stage.status st) then result [(x,s)] s fl
 else if n <= 1 then R.return st
 else reapply (duplicate (n - 1) f) st s fl)
;;

(* s[t]* *)
let iterate_timed t =
 let t = Process.Global (Unix.gettimeofday () +. t) in
 let rec iterate_timed f x = fun s fl ->
  R.(>>=) R.get (fun s' ->
  match fst (Process.run_timed t (execute s fl s' <.> f) x) with
   | None -> result [(x,s)] s fl
   | Some (st,s',_) ->
    R.(>>) (R.set s')
     (if Status.is_fail (Stage.status st) then result [(x,s)] s fl
     else reapply (iterate_timed f) st s fl))
 in
 iterate_timed
;;

(* Specifiers *)
(* s% *)
let stop f x = fun s fl ->
 R.(>>=) (f x s true) (fun st -> R.return (Stage.set_fail_early st false))
;;

(* s! *)
let strict f x = fun s fl ->
 R.(>>=) (f x s fl) (fun st ->
 if Status.is_complete (Stage.status st) then R.return st
 else result [(x,State.set_status Status.fail s)] s fl)
;;

(* s[t] *)
let timed t f x = fun s fl ->
 R.(>>=) R.get (fun s' ->
 match fst (Process.run_timed (Process.Local t) (execute s fl s' <.> f) x) with
  | None -> result [(x,State.set_status Status.fail s)] s fl
  | Some (st,s',_) -> R.(>>) (R.set s') (R.return st))
;;

(* useful functions *)
let finished p = (Proof.make p [Proof.finished],Status.terminating);;
let unfinished p = (Proof.make p [Proof.unfinished],Status.unfinished);;
let nonterminating p = (Proof.make p [Proof.finished],Status.nonterminating);;
let failed = (Proof.unfinished,Status.fail);;

let return2 s p proof status =
 result [((),S.append (S.make p proof status) s)];;

(* Lifting processors *)
let executem_result solve get_result make =
 get >>= fun s -> lift (solve (S.get_problem s)) >>= fun r ->
 let make_s p proof status = S.append (S.make p proof status) s in
 match r with
 | None -> result [((),make_s (S.get_problem s) (Proof.unfinished) Status.fail)]
 | Some r ->
  let proof = make r and r = get_result r in
  if Result.is_no r then result [((),make_s (S.get_problem s)
   (Proof.make proof [Proof.finished]) Status.nonterminating)] else
  match Result.yes r with
  | [] -> result [((),make_s (S.get_problem s)
   (Proof.make proof [Proof.finished]) Status.terminating)]
  | _ -> result (List.map (fun p -> ((),make_s p
   (Proof.make proof [Proof.unfinished]) Status.unfinished)) (Result.yes r))
;;

let executem_list solve get_problems make =
 get >>= fun s -> lift (solve (S.get_problem s)) >>= fun r ->
 let is_empty r = List.for_all Problem.is_empty (get_problems r) in
 let extract p r = if is_empty r then finished p else unfinished p in
 let (proof,status) = option (fun r -> extract (make r) r) failed r in
 let s = S.append (S.make (S.get_problem s) proof status) s in
 result (match Option.map get_problems r with
  | None | Some [] -> [((),s)]
  | Some qs -> List.map (Pair.make () <.> flip S.set_problem s) qs )
;;

let executem solve get_problem make =
  executem_list solve (fun s -> [get_problem s]) make;;

let execute_list solve get_problems make =
  executem_list (R.return <.> solve) get_problems make;;

let execute solve get_problem make =
  executem (R.return <.> solve) get_problem make;;
