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

open Automata

(*** MODULES ******************************************************************)
module F = Rewriting.Function;;
module M = Automata.Monad;;
module R = Rewriting.Monad;;
module S = Rewriting.Signature;;
module T = Rewriting.Trs;;

(*** OPENS ********************************************************************)
open Util;;
open Rewriting;;
open Automata;;

(*** FUNCTIONS ****************************************************************)
(* Tests: Module Term *)
let (>>=) = M.(>>=);;
let (>>) = M.(>>);;

let test =
 Term.of_string ["x";"y";"z"] ["1";"2"] "x" >>= fun r ->
 Term.of_string ["x";"y";"z"] ["1";"2"] "a" >>= fun s ->
 Term.of_string ["x";"y";"z"] ["1";"2"] "f(f(b,a),f(y,x))" >>= fun t ->
 Term.of_string ["x";"y";"z"] ["1";"2"] "g(f(g(1),2))" >>= fun u ->
 Term.of_string ["x";"y";"z"] ["1";"2"] "f(g(1),g(1))" >>= fun v ->
 Term.of_string ["x";"y";"z"] ["1";"2"] "g(g(f(1,2)))" >>= fun w ->
 
 (* function cons *)
 assert (List.length (Term.cons r) = 0);
 assert (List.length (Term.cons s) = 1);
 assert (List.length (Term.cons t) = 2);
 assert (List.length (Term.cons u) = 0);
 assert (List.length (Term.cons v) = 0);
 assert (List.length (Term.cons w) = 0);

 (* function funs *)
 assert (List.length (Term.funs r) = 0);
 assert (List.length (Term.funs s) = 1);
 assert (List.length (Term.funs t) = 3);
 assert (List.length (Term.funs u) = 2);
 assert (List.length (Term.funs v) = 2);
 assert (List.length (Term.funs w) = 2);

 (* function states *)
 assert (List.length (Term.states r) = 0);
 assert (List.length (Term.states s) = 0);
 assert (List.length (Term.states t) = 0);
 assert (List.length (Term.states u) = 2);
 assert (List.length (Term.states v) = 1);
 assert (List.length (Term.states w) = 2);

 (* function vars *)
 assert (List.length (Term.vars r) = 1);
 assert (List.length (Term.vars s) = 0);
 assert (List.length (Term.vars t) = 2);
 assert (List.length (Term.vars u) = 0);
 assert (List.length (Term.vars v) = 0);
 assert (List.length (Term.vars w) = 0);
 
 (* function size *)
 assert (Term.size r = 1);
 assert (Term.size s = 1);
 assert (Term.size t = 7);
 assert (Term.size u = 5);
 assert (Term.size v = 5);
 assert (Term.size w = 5);
 
 (* function min *)
 assert (List.length (Term.min [r;s;t;u]) = 2);
 assert (List.length (Term.min [s;t;u;v]) = 1);
 assert (List.length (Term.min [t;u;v;w]) = 3);
 
 (* function choose *)
 assert (Term.choose [r;t;u] = r);
 assert (Term.choose [t;u;v] = v);
 assert (Term.choose [u;v;w] = v);
 M.return ()
;;

Format.printf "testing module Term         ... ";;
ignore (M.run (S.empty 10,Status.init) test);;
Format.printf "ok@\n";;

(* Tests: Module Rhs *)
let test =
 M.fresh_state >>= fun o -> M.fresh_state >>= fun p ->
 M.fresh_state >>= fun q -> M.fresh_state >>= fun r ->
 let t = Rhs.make None [q;p] [q;p] in
 let u = Rhs.create [q;p] in
 let v = Rhs.make None [q;o;r] [q;r;o;p] in
 let w = Rhs.set_agent o (Rhs.singleton p) in
 let w = Rhs.add q (Rhs.add r w) in

 (* functions make, singleton, create, add *)
 assert (t = u);
 assert (u <> v);
 assert (v = w);

 (* function set_agent *)
 let u = Rhs.set_agent o u in
 let w = Rhs.set_agent r w in
 assert (Option.the (Rhs.agent u) = o);
 assert (Rhs.states u = [o;q;p]);
 assert (Rhs.violations u = []);
 assert (Option.the (Rhs.agent w) = r);
 assert (Rhs.states w = [q;r;o;p]);
 assert (Rhs.violations w = []);

 (* function diff *)
 assert (Rhs.diff t u = None);
 assert (Option.the (Rhs.diff v u) = Rhs.make None [r] [r]);
 assert (Option.the (Rhs.diff v t) = Rhs.make None [o;r] [r;o]);

 (* function inter *)
 assert (Option.the (Rhs.inter t u) = t);
 assert (Option.the (Rhs.inter v u) = Rhs.make None [q;o] [q;o;p]);
 assert (Option.the (Rhs.inter v t) = Rhs.make None [q] [q;p]);

 (* function det *)
 let u = Rhs.det u in
 let w = Rhs.det w in
 assert (Option.the (Rhs.agent u) = o);
 assert (Rhs.states u = [o]);
 assert (Rhs.violations u = []);
 assert (Option.the (Rhs.agent w) = r);
 assert (Rhs.states w = [r]);
 assert (Rhs.violations w = []);
 M.return ()
;;

Format.printf "testing module Rhs          ... ";;
ignore (M.run (S.empty 10,Status.init) test);;
Format.printf "ok@\n";;

(* Tests: Module Automaton *)
let test =
 M.create_state 1 >>= fun p1 -> M.create_state 2 >>= fun p2 ->
 M.create_state 3 >>= fun p3 -> M.create_state 4 >>= fun p4 ->
 M.create_state 5 >>= fun p5 -> M.create_state 6 >>= fun p6 ->
 M.create_state 7 >>= fun p7 -> M.create_state 8 >>= fun p8 ->
 M.create_state 9 >>= fun p9 -> M.create_state 10 >>= fun p10 ->
 M.create_state 11 >>= fun p11 -> M.create_state 12 >>= fun p12 ->
 M.create_state 13 >>= fun p13 -> M.create_state 14 >>= fun p14 ->
 M.create_state 15 >>= fun p15 -> M.create_state 16 >>= fun p16 ->
 M.create_state 17 >>= fun p17 -> M.create_state 18 >>= fun p18 ->
 M.create_state 19 >>= fun p19 -> M.create_state 20 >>= fun p20 ->
 M.get >>= fun (state,_) -> M.set (state,Status.add_state p15 Status.init) >>
 let ps = ["1";"2";"3";"4";"5";"6";"7";"8";"9";"10";"11";"12";"13";"14";"15"] in
 let s = 
  "a -> 1 \
   a -> 2 \
   a -> 3 \
   b -> 4 \
   c -> 3 \
   f(1,4) -> 2 \
   f(2,1) -> 4 \
   f(2,1) -> 5 \
   g(2) -> 3 \
   g(4) -> 1 \
   g(4) -> 3 \
   3 -> 2 \
   2 -> 4"
 in
 Automaton.of_string ps s >>= fun a ->
 let a = Automaton.add_final p3 a in
 let s = 
  "a -> 3 \
   a -> 5 \
   b -> 2 \
   b -> 4 \
   f(1,1) -> 1 \
   f(1,2) -> 1 \
   f(1,3) -> 1 \
   f(2,1) -> 1 \
   f(2,2) -> 1 \
   f(2,3) -> 1 \
   f(3,1) -> 1 \
   f(3,2) -> 1 \
   f(3,3) -> 1 \
   h(1,6) -> 7 \
   h(2,1) -> 1 \
   h(2,1) -> 6 \
   h(2,3) -> 1 \
   h(2,3) -> 8 \
   h(2,5) -> 7 \
   h(3,1) -> 1 \
   h(3,1) -> 7 \
   h(3,3) -> 1 \
   h(3,3) -> 3 \
   h(3,8) -> 2 \
   h(4,2) -> 5 \
   h(5,2) -> 9"
 in
 Automaton.of_string ps s >>= fun b ->
 let b = Automaton.add_final p3 b in
 let s = 
  "f(1,2) -> 1 \
   f(1,2) -> 2 \
   f(2,1) -> 2 \
   f(2,1) -> 3"
 in
 Automaton.of_string ps s >>= fun c ->
 let c = Automaton.add_final p1 c in
 let s = 
  "a -> 1 \
   b -> 4 \
   c -> 3 \
   f(1,3) -> 2 \
   f(4,2) -> 5 \
   f(2,1) -> 4 \
   g(5) -> 6 \
   g(3) -> 5 \
   3 -> 2 \
   2 -> 4 \
   4 -> 3 \
   5 -> 3 \
   6 -> 6"
 in
 Automaton.of_string ps s >>= fun d ->
 let d = Automaton.add_final p1 d in
 let s = 
  "a -> 1 \
   a -> 2 \
   a -> 3 \
   b -> 4 \
   c -> 3 \
   f(1,4) -> 2 \
   f(2,1) -> 4 \
   f(2,1) -> 5 \
   g(2) -> 3 \
   g(4) -> 1 \
   g(4) -> 3 \
   i(1,4,2) -> 3 \
   3 -> 2 \
   2 -> 4"
 in
 Automaton.of_string ps s >>= fun e ->
 let e = Automaton.add_final p3 e in
 let s = 
  "a -> 1 \
   f(1,2) -> 2 \
   g(2) -> 1 \
   g(2) -> 2"
 in
 Automaton.of_string ps s >>= fun f ->
 let f = Automaton.add_final p2 f in
 let s = 
  "a -> 1 \
   a -> 2 \
   b -> 2 \
   f(1,4) -> 2 \
   f(2,5) -> 4 \
   f(2,6) -> 5 \
   g(2) -> 3 \
   g(4) -> 1 \
   g(6) -> 5 \
   5 -> 4 \
   2 -> 3"
 in
 Automaton.of_string ps s >>= fun g ->
 let g = Automaton.set_finals [p1;p3;p4;p6] g in
 let s = 
  "a -> 6 \
   a -> 7 \
   b -> 7 \
   h(6,9) -> 7 \
   h(7,7) -> 9 \
   g(7) -> 6 \
   g(7) -> 8 \
   7 -> 10"
 in
 Automaton.of_string ps s >>= fun h ->
 let h = Automaton.set_finals [p6;p7;p10] h in

 (* function remove *)
 Lhs.of_string ps "a" >>= fun l1 -> Lhs.of_string ps "f(1,4)" >>= fun l2 ->
 Lhs.of_string ps "g(3)" >>= fun l3 -> Lhs.of_string ps "2" >>= fun l4 ->
 Automaton.remove l1 a >>= fun a -> assert (Automaton.size a = 10);
 Automaton.remove l2 a >>= fun a -> assert (Automaton.size a = 9);
 Automaton.remove l3 a >>= fun a -> assert (Automaton.size a = 9);
 Automaton.remove l4 a >>= fun a -> assert (Automaton.size a = 8);

 (* function update *)
 Automaton.update l1 p1 a >>= fun a -> assert (Automaton.size a = 9);
 Automaton.update l1 p2 a >>= fun a -> assert (Automaton.size a = 10);
 Automaton.update l2 p3 a >>= fun a -> assert (Automaton.size a = 11);
 Automaton.update l4 p4 a >>= fun a -> assert (Automaton.size a = 12);

 (* function add *)
 let r1 = Rhs.create [p2;p1] in
 let r2 = Rhs.create [p5;p6] in
 let r4 = Rhs.singleton p5 in
 Automaton.add l1 r1 a >>= fun a ->
 assert (Automaton.size a = 12);
 Automaton.remove l1 a >>= Automaton.add l1 r1 >>= fun a ->
 assert (Automaton.size a = 12);
 Automaton.remove l2 a >>= Automaton.add l2 r2 >>= fun a ->
 assert (Automaton.size a = 13);
 Automaton.remove l4 a >>= Automaton.add l4 r4 >>= fun a ->
 assert (Automaton.size a = 13);

 (* function add *)
 let r1 = Rhs.create [p3;p2;p1] in
 let r2 = Rhs.singleton p2 in
 let r4 = Rhs.singleton p4 in
 Automaton.replace l1 r1 a >>= fun a -> assert (Automaton.size a = 14);
 Automaton.replace l2 r2 a >>= fun a -> assert (Automaton.size a = 13);
 Automaton.replace l4 r4 a >>= fun a -> assert (Automaton.size a = 13);

 (* function add_final *)
 let a = Automaton.add_final p5 a in
 assert (List.length (Automaton.finals a) = 2);
 let a = Automaton.add_final p4 a in
 assert (List.length (Automaton.finals a) = 3);
 let a = Automaton.add_final p3 a in
 assert (List.length (Automaton.finals a) = 3);

 (* function remove_final *)
 let a = Automaton.remove_final p5 a in
 assert (List.length (Automaton.finals a) = 2);
 let a = Automaton.remove_final p4 a in
 assert (List.length (Automaton.finals a) = 1);
 let a = Automaton.remove_final p4 a in
 assert (List.length (Automaton.finals a) = 1);

 (* function remove_final *)
 let a = Automaton.set_finals [p4;p5] a in
 assert (List.length (Automaton.finals a) = 2);
 let a = Automaton.set_finals [] a in
 assert (List.length (Automaton.finals a) = 0);
 let a = Automaton.set_finals [p3] a in
 assert (List.length (Automaton.finals a) = 1);

 (* function states *)
 Lhs.of_string ps "f(6,7)" >>= fun l5 -> Lhs.of_string ps "8" >>= fun l6 ->
 assert (List.length (Automaton.states ~i:false a) = 5);
 assert (List.length (Automaton.states ~i:true a) = 5);
 Automaton.replace l2 (Rhs.create [p2;p4;p5]) a >>= fun a ->
 assert (List.length (Automaton.states ~i:false a) = 5);
 assert (List.length (Automaton.states ~i:true a) = 5);
 Automaton.replace l5 (Rhs.create [p2;p3]) a >>= fun a ->
 assert (List.length (Automaton.states ~i:false a) = 7);
 assert (List.length (Automaton.states ~i:true a) = 5);
 Automaton.replace l6 (Rhs.singleton p7) a >>= fun a ->
 assert (List.length (Automaton.states ~i:false a) = 8);
 assert (List.length (Automaton.states ~i:true a) = 6);
 Automaton.replace l2 (Rhs.singleton p2) a >>= fun a ->
 Automaton.remove l5 a >>= fun a ->
 Automaton.remove l6 a >>= fun a ->

 (* function finals *)
 assert (List.length (Automaton.finals ~i:false a) = 1);
 assert (List.length (Automaton.finals ~i:true a) = 1);
 let a = Automaton.add_final p4 a in
 assert (List.length (Automaton.finals ~i:false a) = 2);
 assert (List.length (Automaton.finals ~i:true a) = 2);
 Automaton.replace l5 (Rhs.create [p2;p4]) a >>= fun a ->
 Automaton.replace l5 (Rhs.create [p2;p4]) a >>= fun a ->
 let a = Automaton.add_final p6 a in
 assert (List.length (Automaton.finals ~i:false a) = 3);
 assert (List.length (Automaton.finals ~i:true a) = 2);
 let a = Automaton.set_finals [p3] a in
 Automaton.remove l5 a >>= fun a ->
 Automaton.remove l6 a >>= fun a ->

 (* function trans *)
 let funs l r = Lhs.root l = Lhs.root l2 in
 let states l r = Rhs.mem p3 r in
 let cons l r = l = l1 in
 assert (List.length (Automaton.trans a) = 9);
 assert (List.length (Automaton.trans ~p:funs a) = 2);
 assert (List.length (Automaton.trans ~p:states a) = 4);
 assert (List.length (Automaton.trans ~p:cons a) = 1);
 Automaton.replace l5 (Rhs.create [p2;p3]) a >>= fun a ->
 assert (List.length (Automaton.trans a) = 10);
 assert (List.length (Automaton.trans ~p:funs a) = 3);
 assert (List.length (Automaton.trans ~p:states a) = 5);
 assert (List.length (Automaton.trans ~p:cons a) = 1);
 Automaton.remove l5 a >>= fun a ->

 (* function find TODO test optional flag c *)
 Automaton.find l1 a >>= fun r1 ->
 assert (Option.the r1 = Rhs.create [p3;p2;p1]);
 Automaton.find l2 a >>= fun r2 ->
 assert (Option.the r2 = Rhs.singleton p2);
 Automaton.find l5 a >>= fun r5 ->
 assert (r5 = None);

 (* test function adapt *)
 (*
 a / b: a -> 3
        b -> 4

 a / d: a -> 1
        b -> 4
        c -> 3
        f(2,1) -> 4
        3 -> 2
        2 -> 4

 a / e: a -> 1
        a -> 2
        a -> 3
        b -> 4
        c -> 3
        f(1,4) -> 2
        f(2,1) -> 4
        f(2,1) -> 5
        g(2) -> 3
        g(4) -> 1
        g(4) -> 3
        3 -> 2
        2 -> 4
 *)
 Automaton.adapt (Automaton.copy a) b >>= fun a' ->
 Lhs.of_string ps "a" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p3 (Option.the r));
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 assert (Automaton.size a' = 2);

 Automaton.adapt (Automaton.copy a) d >>= fun a' ->
 Lhs.of_string ps "a" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 Lhs.of_string ps "c" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p3 (Option.the r));
 Lhs.of_string ps "f(2,1)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 Lhs.of_string ps "3" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p2 (Option.the r));
 Lhs.of_string ps "2" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 assert (Automaton.size a' = 6);

 Automaton.adapt (Automaton.copy a) e >>= fun a' ->
 Lhs.of_string ps "a" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p2 (Option.the r));
 assert (Rhs.mem p3 (Option.the r));
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 Lhs.of_string ps "c" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p3 (Option.the r));
 Lhs.of_string ps "f(1,4)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p2 (Option.the r));
 Lhs.of_string ps "f(2,1)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 assert (Rhs.mem p5 (Option.the r));
 Lhs.of_string ps "g(2)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p3 (Option.the r));
 Lhs.of_string ps "g(4)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p3 (Option.the r));
 Lhs.of_string ps "3" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p2 (Option.the r));
 Lhs.of_string ps "2" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 assert (Automaton.size a' = 13);

 (* test function inter *)
 (*
 a inter b: a -> (1,3),(1,5),(2,3),(2,5),(3,3),(3,5),(4,3),(4,5)
            b -> (4,2),(4,4)
            f((1,1),(4,1)) -> (2,1),(4,1)
            f((1,1),(4,2)) -> (2,1),(4,1)
            f((1,1),(4,3)) -> (2,1),(4,1)
            f((1,2),(4,1)) -> (2,1),(4,1)
            f((1,2),(4,2)) -> (2,1),(4,1)
            f((1,2),(4,3)) -> (2,1),(4,1)
            f((1,3),(4,1)) -> (2,1),(4,1)
            f((1,3),(4,2)) -> (2,1),(4,1)
            f((1,3),(4,3)) -> (2,1),(4,1)
            f((2,1),(1,1)) -> (4,1),(5,1)
            f((2,1),(1,2)) -> (4,1),(5,1)
            f((2,1),(1,3)) -> (4,1),(5,1)
            f((2,2),(1,1)) -> (4,1),(5,1)
            f((2,2),(1,2)) -> (4,1),(5,1)
            f((2,2),(1,3)) -> (4,1),(5,1)
            f((2,3),(1,1)) -> (4,1),(5,1)
            f((2,3),(1,2)) -> (4,1),(5,1)
            f((2,3),(1,3)) -> (4,1),(5,1)

            final states: (3,3)
           
            reduced: a -> (1,3),(1,5),(2,3),(2,5),(3,3),(3,5),(4,3),(4,5)
                     b -> (4,2),(4,4)
                     f((1,3),(4,1)) -> (2,1),(4,1)
                     f((1,3),(4,2)) -> (2,1),(4,1)
                     f((1,3),(4,3)) -> (2,1),(4,1)
                     f((2,1),(1,3)) -> (4,1),(5,1)
                     f((2,3),(1,3)) -> (4,1),(5,1)

 a inter d: a -> (1,1),(2,1),(3,1),(4,1)
            b -> (4,2),(4,3),(4,4)
            c -> (2,2),(2,3),(2,4),(3,2),(3,3),(3,4),(4,2),(4,3),(4,4)
            f((1,1),(4,3)) -> (2,2),(2,3),(2,4),(4,2),(4,3),(4,4)
            f((1,4),(4,2)) -> (2,2),(2,3),(2,4),(4,2),(4,3),(4,4),(2,5),(4,5)
            f((1,2),(4,1)) -> (2,2),(2,3),(2,4),(4,2),(4,3),(4,4)
            f((2,1),(1,3)) -> (4,2),(4,3),(4,4),(5,2),(5,3),(5,4)
            f((2,4),(1,2)) -> (4,2),(4,3),(4,4),(5,2),(5,3),(5,4),(4,5),(5,5)
            f((2,2),(1,1)) -> (4,2),(4,3),(4,4),(5,2),(5,3),(5,4)
            g((2,5)) -> (2,6),(3,6),(4,6)
            g((2,3)) -> (2,2),(2,3),(2,4),(2,5),(3,2),(3,3),(3,4),(3,5),
                        (4,2),(4,3),(4,4),(4,5)
            g((4,5)) -> (1,6),(2,6),(3,6),(4,6)
            g((4,3)) -> (1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4),(2,5),
                        (3,2),(3,3),(3,4),(3,5),(4,2),(4,3),(4,4),(4,5)

            final states: (3,1)

            reduced: same automaton

 a inter -: -
 *)
 M.get >>= fun (state,status) -> M.set (state,Status.init) >>
 let b' = Automaton.add_final p5 (Automaton.copy b) in
 Automaton.inter a b' >>= fun a' ->
 Lhs.of_string ps "a" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p2 (Option.the r));
 assert (Rhs.mem p3 (Option.the r));
 assert (Rhs.mem p4 (Option.the r));
 assert (Rhs.mem p5 (Option.the r));
 assert (Rhs.mem p6 (Option.the r));
 assert (Rhs.mem p7 (Option.the r));
 assert (Rhs.mem p8 (Option.the r));
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p12 (Option.the r));
 assert (Rhs.mem p16 (Option.the r));
 Lhs.of_string ps "f(6,8)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p9 (Option.the r));
 assert (Rhs.mem p14 (Option.the r));
 Lhs.of_string ps "f(8,2)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p9 (Option.the r));
 assert (Rhs.mem p10 (Option.the r));
 Lhs.of_string ps "f(8,9)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p9 (Option.the r));
 assert (Rhs.mem p10 (Option.the r));
 Lhs.of_string ps "f(8,12)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p9 (Option.the r));
 assert (Rhs.mem p10 (Option.the r));
 Lhs.of_string ps "f(10,8)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p9 (Option.the r));
 assert (Rhs.mem p14 (Option.the r));
 assert (Automaton.finals a' = [p4;p3]);
 assert (Automaton.size a' = 20);

 M.set (state,Status.init) >> Automaton.inter a d >>= fun a' ->
 Lhs.of_string ps "a" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.size (Option.the r) = 4);
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.size (Option.the r) = 3);
 Lhs.of_string ps "c" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.size (Option.the r) = 9);
 Lhs.of_string ps "f(23,13)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.size (Option.the r) = 8);
 Lhs.of_string ps "f(3,21)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.size (Option.the r) = 6);
 Lhs.of_string ps "f(4,12)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.size (Option.the r) = 6);
 Lhs.of_string ps "f(22,1)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.size (Option.the r) = 6);
 Lhs.of_string ps "f(11,22)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.size (Option.the r) = 8);
 Lhs.of_string ps "f(10,4)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.size (Option.the r) = 6);
 Lhs.of_string ps "g(15)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.size (Option.the r) = 4);
 Lhs.of_string ps "g(5)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.size (Option.the r) = 3);
 Lhs.of_string ps "g(12)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.size (Option.the r) = 16);
 Lhs.of_string ps "g(9)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.size (Option.the r) = 12);
 assert (Automaton.finals a' = [p2]);
 assert (Automaton.size a' = 91);

 Automaton.inter a (Automaton.create 0) >>= fun a' ->
 assert (Automaton.finals a' = []);
 assert (Automaton.size a' = 0);
 M.get >>= fun (state,_) -> M.set (state,status) >>

 (* test function analgoies *)
 M.get >>= fun (state,status) -> M.set (state,Status.init) >>
 Automaton.analogies a b >>= fun qs ->
 assert (List.mem (p1,p3) qs);
 assert (List.mem (p1,p5) qs);
 assert (List.mem (p2,p1) qs);
 assert (List.mem (p2,p3) qs);
 assert (List.mem (p2,p5) qs);
 assert (List.mem (p3,p3) qs);
 assert (List.mem (p3,p5) qs);
 assert (List.mem (p4,p1) qs);
 assert (List.mem (p4,p2) qs);
 assert (List.mem (p4,p3) qs);
 assert (List.mem (p4,p4) qs);
 assert (List.mem (p4,p5) qs);
 assert (List.mem (p5,p1) qs);
 assert (List.length qs = 13);

 M.set (state,Status.init) >> Automaton.analogies a d >>= fun qs ->
 assert (List.mem (p1,p1) qs);
 assert (List.mem (p1,p2) qs);
 assert (List.mem (p1,p3) qs);
 assert (List.mem (p1,p4) qs);
 assert (List.mem (p1,p5) qs);
 assert (List.mem (p1,p6) qs);
 assert (List.mem (p2,p1) qs);
 assert (List.mem (p2,p2) qs);
 assert (List.mem (p2,p3) qs);
 assert (List.mem (p2,p4) qs);
 assert (List.mem (p2,p5) qs);
 assert (List.mem (p2,p6) qs);
 assert (List.mem (p3,p1) qs);
 assert (List.mem (p3,p2) qs);
 assert (List.mem (p3,p3) qs);
 assert (List.mem (p3,p4) qs);
 assert (List.mem (p3,p5) qs);
 assert (List.mem (p3,p6) qs);
 assert (List.mem (p4,p1) qs);
 assert (List.mem (p4,p2) qs);
 assert (List.mem (p4,p3) qs);
 assert (List.mem (p4,p4) qs);
 assert (List.mem (p4,p5) qs);
 assert (List.mem (p4,p6) qs);
 assert (List.mem (p5,p2) qs);
 assert (List.mem (p5,p3) qs);
 assert (List.mem (p5,p4) qs);
 assert (List.mem (p5,p5) qs);
 assert (List.length qs = 28);

 Automaton.analogies a (Automaton.create 0) >>= fun qs ->
 assert (qs = []);
 M.get >>= fun (state,_) -> M.set (state,status) >>

 (* test function minus *)
 (*
 a - b: a -> 1
        a -> 2
        c -> 3
        f(1,4) -> 2
        f(2,1) -> 4
        f(2,1) -> 5
        g(2) -> 3
        g(4) -> 1
        g(4) -> 3
        3 -> 2
        2 -> 4

 a - d: a -> 2
        a -> 3
        f(1,4) -> 2
        f(2,1) -> 5
        g(2) -> 3
        g(4) -> 1
        g(4) -> 3

 a - e: -
 *)
 Automaton.minus (Automaton.copy a) b >>= fun a' ->
 Lhs.of_string ps "a" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p2 (Option.the r));
 assert (Automaton.size a' = 11);

 Automaton.minus (Automaton.copy a) d >>= fun a' ->
 Lhs.of_string ps "a" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p2 (Option.the r));
 assert (Rhs.mem p3 (Option.the r));
 Lhs.of_string ps "f(2,1)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 assert (Automaton.size a' = 7);

 Automaton.minus (Automaton.copy a) e >>= fun a' ->
 assert (Automaton.size a' = 0);

 (* test function restrict *)
 (*
 fs : [a;b;c;f;g]

 a -> 1
 a -> 2
 a -> 3
 b -> 4
 c -> 3
 f(1,4) -> 2
 f(2,1) -> 4
 f(2,1) -> 5
 g(2) -> 3
 g(4) -> 1
 g(4) -> 3
 3 -> 2
 2 -> 4

 fs : [a;c;f]

 a -> 1
 a -> 2
 a -> 3
 c -> 3
 f(1,4) -> 2
 f(2,1) -> 4
 f(2,1) -> 5
 3 -> 2
 2 -> 4

 fs : []

 3 -> 2
 2 -> 4
 *)
 
 M.create_fun 0 "a" >>= fun fa -> M.create_fun 0 "b" >>= fun fb ->
 M.create_fun 0 "c" >>= fun fc -> M.create_fun 1 "g" >>= fun fg ->
 M.create_fun 2 "f" >>= fun ff ->

 let size f a =
  Automaton.fold (fun l r n ->
   if Option.fold ((=) f) false (Lhs.root l) then n+(Rhs.size r) else n) a 0
 in

 Automaton.restrict [fa;fb;fc;ff;fg] (Automaton.copy a) >>= fun a' ->
 assert (size fa a' = 3);
 assert (size fb a' = 1);
 assert (size fc a' = 1);
 assert (size ff a' = 3);
 assert (size fg a' = 3);
 assert (Automaton.size a' = 13);

 Automaton.restrict [fa;fc;ff] (Automaton.copy a) >>= fun a' ->
 assert (size fa a' = 3);
 assert (size fc a' = 1);
 assert (size ff a' = 3);
 assert (Automaton.size a' = 9);

 Automaton.restrict [] (Automaton.copy a) >>= fun a' ->
 assert (Automaton.size a' = 2);

 (* test function reduce *)
 (*
 a: a -> 1
    a -> 2
    a -> 3
    b -> 4
    c -> 3
    f(1,4) -> 2
    f(2,1) -> 4
    f(2,1) -> 5
    g(2) -> 3
    g(4) -> 1
    g(4) -> 3
    3 -> 2
    2 -> 4

 g: a -> 1
    a -> 2
    b -> 2
    g(2) -> 3
    2 -> 3
 *)

 Automaton.reduce (Automaton.copy a) >>= fun a' ->
 assert (size fa a' = 3);
 assert (size fb a' = 1);
 assert (size fc a' = 1);
 assert (size ff a' = 3);
 assert (size fg a' = 3);
 assert (Automaton.size a' = 13);
 assert (Automaton.size a' = 13);
 assert (Automaton.finals a' = [p3]);

 Automaton.reduce (Automaton.copy g) >>= fun g' ->
 Lhs.of_string ps "a" >>= fun l -> Automaton.find l g' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p2 (Option.the r));
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l g' >>= fun r ->
 assert (Rhs.mem p2 (Option.the r));
 Lhs.of_string ps "g(2)" >>= fun l -> Automaton.find l g' >>= fun r ->
 assert (Rhs.mem p3 (Option.the r));
 assert (Automaton.size g' = 5);
 assert (Automaton.finals g' = [p1;p3]);

 (* function combine *)
 (*
 combine a d: a -> 1,2,3
              b -> 4
              c -> 3
              f(1,3) -> 2
              f(1,4) -> 2
              f(2,1) -> 4,5
              f(4,2) -> 5
              g(2) -> 3
              g(3) -> 5
              g(4) -> 1,3
              g(5) -> 6
              3 -> 2
              2 -> 4
              4 -> 3
              5 -> 3

 combine a h: a -> 1,2,3,6,7
              b -> 4,7
              c -> 3
              f(1,4) -> 2
              f(2,1) -> 4,5
              g(2) -> 3
              g(4) -> 1,3
              g(7) -> 6,8
              h(6,9) -> 7
              h(7,7) -> 9
              3 -> 2
              2 -> 4
              7 -> 10
 *)
 Automaton.combine (Automaton.copy a) a >>= fun a' ->
 assert (a = a);

 Automaton.combine (Automaton.copy a) d >>= fun a' ->
 Lhs.of_string ps "a" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p2 (Option.the r));
 assert (Rhs.mem p3 (Option.the r));
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 Lhs.of_string ps "c" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p3 (Option.the r));
 Lhs.of_string ps "f(1,3)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p2 (Option.the r));
 Lhs.of_string ps "f(1,4)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p2 (Option.the r));
 Lhs.of_string ps "f(2,1)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 assert (Rhs.mem p5 (Option.the r));
 Lhs.of_string ps "f(4,2)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 Lhs.of_string ps "g(2)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p3 (Option.the r));
 Lhs.of_string ps "g(3)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 Lhs.of_string ps "g(4)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p3 (Option.the r));
 Lhs.of_string ps "g(5)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p6 (Option.the r));
 Lhs.of_string ps "2" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 Lhs.of_string ps "3" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p2 (Option.the r));
 Lhs.of_string ps "4" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p3 (Option.the r));
 Lhs.of_string ps "5" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p3 (Option.the r));
 assert (Automaton.size a' = 19);
 assert (Automaton.finals a' = [p3]);

 Automaton.combine (Automaton.copy a) h >>= fun a' ->
 Lhs.of_string ps "a" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p2 (Option.the r));
 assert (Rhs.mem p3 (Option.the r));
 assert (Rhs.mem p6 (Option.the r));
 assert (Rhs.mem p7 (Option.the r));
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 assert (Rhs.mem p7 (Option.the r));
 Lhs.of_string ps "c" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p3 (Option.the r));
 Lhs.of_string ps "f(1,4)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p2 (Option.the r));
 Lhs.of_string ps "f(2,1)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 assert (Rhs.mem p5 (Option.the r));
 Lhs.of_string ps "g(2)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p3 (Option.the r));
 Lhs.of_string ps "g(4)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p3 (Option.the r));
 Lhs.of_string ps "g(7)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p6 (Option.the r));
 assert (Rhs.mem p8 (Option.the r));
 Lhs.of_string ps "h(6,9)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p7 (Option.the r));
 Lhs.of_string ps "h(7,7)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p9 (Option.the r));
 Lhs.of_string ps "2" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 Lhs.of_string ps "3" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p2 (Option.the r));
 Lhs.of_string ps "7" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p10 (Option.the r));
 assert (Automaton.size a' = 21);
 assert (Automaton.finals a' = [p3]);

 (* function union *)
 Automaton.union (Automaton.copy a) h >>= fun a' ->
 Lhs.of_string ps "a" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p2 (Option.the r));
 assert (Rhs.mem p3 (Option.the r));
 assert (Rhs.mem p6 (Option.the r));
 assert (Rhs.mem p7 (Option.the r));
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 assert (Rhs.mem p7 (Option.the r));
 Lhs.of_string ps "c" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p3 (Option.the r));
 Lhs.of_string ps "f(1,4)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p2 (Option.the r));
 Lhs.of_string ps "f(2,1)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 assert (Rhs.mem p5 (Option.the r));
 Lhs.of_string ps "g(2)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p3 (Option.the r));
 Lhs.of_string ps "g(4)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p3 (Option.the r));
 Lhs.of_string ps "g(7)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p6 (Option.the r));
 assert (Rhs.mem p8 (Option.the r));
 Lhs.of_string ps "h(6,9)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p7 (Option.the r));
 Lhs.of_string ps "h(7,7)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p9 (Option.the r));
 Lhs.of_string ps "2" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 Lhs.of_string ps "3" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p2 (Option.the r));
 Lhs.of_string ps "7" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p10 (Option.the r));
 assert (Automaton.size a' = 21);
 assert (Automaton.finals a' = [p10;p7;p6;p3]);

 (* function ec_states *)
 assert (Automaton.ec_states [p1;p4] a = [p4;p1]);
 assert (Automaton.ec_states [p1;p3] a = [p4;p2;p3;p1]);
 assert (Automaton.ec_states [p1;p2;p3] a = [p4;p3;p2;p1]);
 assert (Automaton.ec_states [] a = []);

 (* function ec_rhs *)
 assert (Automaton.ec_rhs (Rhs.create [p1;p4]) a = Rhs.create [p1;p4]);
 assert (Automaton.ec_rhs (Rhs.create [p1;p3]) a = Rhs.create [p2;p4;p1;p3]);
 assert (Automaton.ec_rhs (Rhs.create [p1;p2;p3]) a = Rhs.create [p4;p1;p2;p3]);

 (* function ec *)
 assert (Automaton.size (Automaton.ec ~r:false (Automaton.copy a)) = 21);
 assert (Automaton.size (Automaton.ec ~r:true (Automaton.copy a)) = 19);
 assert (Automaton.size (Automaton.ec ~r:false (Automaton.copy d)) = 26);
 assert (Automaton.size (Automaton.ec ~r:true (Automaton.copy d)) = 22);

 (* function paths TODO test optional flag c *)
 (*
 let printf t ps =
  Format.printf "paths ";
  Term.fprintfm Format.std_formatter t >>= fun _ ->
  Format.printf ":@\n";
  M.fprintf (fun fmt (ps,q) ->
   Format.fprintf fmt "@\nto %a:@\n" State.fprintf q;
   M.fprintf (fun fmt (u,s) ->
    Format.fprintf fmt "("; Term.fprintfm fmt u >>= fun _ ->
    M.return (Format.fprintf fmt ",%a)" Substitution.fprintf s)) "@\n" fmt ps)
   "@\n" Format.std_formatter ps
 in

 automaton:
 
 a -> 3,2,1
 b -> 4
 c -> 3
 f(1,4) -> 2
 f(2,1) -> 5,4
 g(2) -> 3
 g(4) -> 3,1
 2 -> 4
 3 -> 2
 
 history:
 
 a -> 1
 g(2) -> 3
 
 term f(x,f(a,x/y)):
 
 a -> 1,2,3,4
 f(a,1) -> 4,5
 f(a,4) -> 2,4
 f(1,f(a,1)) -> 2
 f(1,f(a,4)) -> 2
 
 with history: f(1,f(a,4)) -> 2
 
 term f(a,g(b)):
 
 a -> 1,2,3,4
 b -> 4
 g(b) -> 1,2,3,4
 f(a,g(b)) -> 2,4,5
 
 with history: f(a,g(b)) -> 2
 
 term g(f(x,g(y))):
 
 g(2) -> 2,3,4
 g(4) -> 1,2,3,4
 f(1,g(2)) -> 2,4
 f(1,g(4)) -> 2,4
 f(2,g(4)) -> 4,5
 g(f(1,g(2))) -> 1,3
 g(f(1,g(4))) -> 1,3
 g(f(2,g(4))) -> 1,3
 
 with history:
 g(f(1,g(2))) -> 1,3
 g(f(1,g(4))) -> 3
 *)

 let vs = ["x";"y";"z"] in
 Term.of_string vs ps "f(x,f(a,x))" >>= fun s ->
 Term.of_string vs ps "f(x,f(a,y))" >>= fun t ->
 Term.of_string vs ps "f(a,g(b))" >>= fun u ->
 Term.of_string vs ps "g(f(x,g(y)))" >>= fun v ->
 M.create_var "x" >>= fun x -> M.create_var "y" >>= fun y ->

 Automaton.paths s a >>= fun paths ->
 let sub = Substitution.singleton x p1 in
 assert (List.mem ([(s,sub)],p2) paths);
 assert (List.length paths = 1);

 Automaton.paths t a >>= fun paths ->
 let sub = Substitution.add y p1 (Substitution.singleton x p1) in
 let sub' = Substitution.add y p4 (Substitution.singleton x p1) in
 assert (List.mem ([(t,sub);(t,sub')],p2) paths);
 assert (List.length paths = 1);

 Automaton.paths u a >>= fun paths ->
 let sub = Substitution.empty in
 assert (List.mem ([(u,sub)],p2) paths);
 assert (List.mem ([(u,sub)],p4) paths);
 assert (List.mem ([(u,sub)],p5) paths);
 assert (List.length paths = 3);

 Automaton.paths v a >>= fun paths ->
 let sub = Substitution.add y p4 (Substitution.singleton x p2) in
 let sub' = Substitution.add y p4 (Substitution.singleton x p1) in
 let sub'' = Substitution.add y p2 (Substitution.singleton x p1) in
 assert (List.mem ([(v,sub);(v,sub');(v,sub'')],p1) paths);
 assert (List.mem ([(v,sub'');(v,sub');(v,sub)],p3) paths);
 assert (List.length paths = 2);

 Automaton.of_string ps "a -> 1 g(2) -> 3" >>= fun h ->
 Automaton.paths ~h:(Some h) s a >>= fun paths ->
 assert (paths = []);

 Automaton.paths ~h:(Some h) t a >>= fun paths ->
 let sub = Substitution.add y p4 (Substitution.singleton x p1) in
 assert (List.mem ([(t,sub)],p2) paths);
 assert (List.length paths = 1);

 Automaton.paths ~h:(Some h) u a >>= fun paths ->
 let sub = Substitution.empty in
 assert (List.mem ([(u,sub)],p2) paths);
 assert (List.length paths = 1);

 Automaton.paths ~h:(Some h) v a >>= fun paths ->
 let sub = Substitution.add y p2 (Substitution.singleton x p1) in
 let sub' = Substitution.add y p4 (Substitution.singleton x p1) in
 assert (List.mem ([(v,sub)],p1) paths);
 assert (List.mem ([(v,sub);(v,sub')],p3) paths);
 assert (List.length paths = 2);

 (*
 automaton:
 
 16 = {1,2,3,4}
 17 = {2,3,4}
 18 = {2,4}
 19 = {4,5}
 20 = {2,4,5}
 
 a -> 1,2,3,4,16
 b -> 4
 c -> 2,3,4,17
 f(1,4) -> 2,4,18
 f(1,16) -> 18
 f(1,17) -> 18
 f(1,18) -> 18
 f(1,19) -> 18
 f(1,20) -> 18
 f(2,1) -> 4,5,19
 f(2,16) -> 19
 f(16,1) -> 19
 f(16,4) -> 18
 f(16,16) -> 20
 f(16,17) -> 18
 f(16,18) -> 18
 f(16,19) -> 18
 f(16,20) -> 18
 f(17,1) -> 19
 f(17,16) -> 19
 f(18,1) -> 19
 f(18,16) -> 19
 f(20,1) -> 19
 f(20,16) -> 19
 g(2) -> 2,3,4,17
 g(4) -> 1,2,3,4,16
 g(16) -> 16
 g(17) -> 16
 g(18) -> 16
 g(19) -> 16
 g(20) -> 16
 2 -> 4
 3 -> 2
 
 term f(x,f(a,x/y)):
 reachable states: 18,19,20
 
 a -> 1,2,3,4,16
 f(a,1) -> 4,5,19
 f(a,4) -> 2,4,18
 f(a,17|18|19|20) -> 18
 f(a,16) -> 18,19,20
 
 f(1,f(a,1)) -> 2,4,18
 f(1,f(a,4)) -> 2,4,18
 f(1,f(a,17|18|19|20)) -> 18
 f(1,f(a,16)) -> 18
 f(16,f(a,1)) -> 18
 f(16,f(a,4)) -> 18
 f(16,f(a,17|18|19|20)) -> 18
 f(16,f(a,16)) -> 18
 
 deterministic: f(1|16,f(a,1|4|16|17|18|19|20)) -> 18
 
 term f(a,g(b)):
 reachable states: 18,19,20
 
 a -> 1,2,3,4,16
 b -> 4
 g(b) -> 1,2,3,4,16
 f(a,g(b)) -> 2,4,5,18,19,20
 
 deterministic: f(a,g(b)) -> 20
 
 term g(f(x,g(y))):
 reachable states: 16,17
 
 g(2) -> 2,3,4,17
 g(4) -> 1,2,3,4,16
 g(16|17|18|19|20) -> 16
 
 f(1,g(2)) -> 2,4,18
 f(16,g(2)) -> 18
 f(1,g(4)) -> 2,4,18
 f(16,g(4)) -> 18,19,20
 f(2,g(4)) -> 4,5,19
 f(17|18|20,g(4)) -> 19
 f(1,g(16|17|18|19|20)) -> 18
 f(16,g(16|17|18|19|20)) -> 20
 f(2|17|18|20,g(16|17|18|19|20)) -> 19
 
 g(f(1,g(2))) -> 1,2,3,4,16,17
 g(f(16,g(2))) -> 16
 g(f(1,g(4))) -> 1,2,3,4,16,17
 g(f(16,g(4))) -> 16
 g(f(2,g(4))) -> 1,2,3,4,16
 g(f(17|18|20,g(4))) -> 16
 g(f(1,g(16|17|18|19|20))) -> 16
 g(f(16,g(16|17|18|19|20))) -> 16
 g(f(2|17|18|20,g(16|17|18|19|20))) -> 16
 
 deterministic: g(f(1|16,g(2))) -> 16
                g(f(1,g(4|16|17|18|19|20))) -> 16
                g(f(16,g(4|16|17|18|19|20))) -> 16
                g(f(2|17|18|20,g(4|16|17|18|19|20))) -> 16
 *)

 Automaton.quasi_det (Automaton.copy a) >>= fun a' ->
 Automaton.paths s a' >>= fun paths ->
 assert (List.length (fst (List.hd paths)) = 2);
 assert (List.length paths = 1);

 Automaton.paths t a' >>= fun paths ->
 assert (List.length (fst (List.hd paths)) = 14);
 assert (List.length paths = 1);

 Automaton.paths u a' >>= fun paths ->
 assert (List.length (fst (List.hd paths)) = 1);
 assert (List.length paths = 1);

 Automaton.paths v a' >>= fun paths ->
 assert (List.length (fst (List.hd paths)) = 38);
 assert (List.length paths = 1);

 (* function rewrite TODO test optional flag c *)
 (*
 let printf t ts =
  Format.printf "@\nnormal forms of ";
  Term.fprintfm Format.std_formatter t >>= fun _ ->
  Format.printf ":@\n"; 
  M.fprintf Term.fprintfm "@\n" Format.std_formatter ts
 in

 automaton:
 
 a -> 3,2,1
 b -> 4
 c -> 3
 f(1,4) -> 2
 f(2,1) -> 5,4
 g(2) -> 3
 g(4) -> 3,1
 2 -> 4
 3 -> 2
 
 term f(g(a),f(2,a)):

 a -> 1,2,3,4
 g(a) -> 1,2,3,4
 f(2,a) -> 4,5
 f(g(a),f(2,a)) -> 2

 term f(f(a,b),g(a)):

 a -> 1,2,3,4
 b -> 4
 f(a,b) -> 2,4
 g(a) -> 1,2,3,4
 f(f(a,b),g(a)) -> 4,5

 term f(f(g(a),f(2,a)),f(f(a,b),g(a))):

 f(g(a),f(2,a)) -> 2
 f(f(a,b),g(a)) -> 4,5
 f(f(g(a),f(2,a)),f(f(a,b),g(a))) -> f(2,4),f(2,5)

 term f(g(a),x):
 
 a -> 1,2,3,4
 g(a) -> 1,3
 f(1|3,x)

 term 3: 3 -> 3
 *)

 Term.of_string vs ps "f(g(a),f(2,a))" >>= fun s ->
 Term.of_string vs ps "f(f(a,b),g(a))" >>= fun t ->
 Term.of_string vs ps "f(f(g(a),f(2,a)),f(f(a,b),g(a)))" >>= fun u ->
 Term.of_string vs ps "f(g(a),x)" >>= fun v ->
 Term.of_string vs ps "3" >>= fun w ->

 Automaton.rewrite s a >>= fun ts ->
 assert (List.mem (Term.State p2) ts);
 assert (List.length ts = 1);

 Automaton.rewrite t a >>= fun ts ->
 assert (List.mem (Term.State p4) ts);
 assert (List.mem (Term.State p5) ts);
 assert (List.length ts = 2);

 Automaton.rewrite u a >>= fun ts ->
 Term.of_string vs ps "f(2,4)" >>= fun nf ->
 assert (List.mem nf ts);
 Term.of_string vs ps "f(2,5)" >>= fun nf ->
 assert (List.mem nf ts);
 assert (List.length ts = 2);

 Automaton.rewrite v a >>= fun ts ->
 Term.of_string vs ps "f(1,x)" >>= fun nf ->
 assert (List.mem nf ts);
 Term.of_string vs ps "f(3,x)" >>= fun nf ->
 assert (List.mem nf ts);
 assert (List.length ts = 2);

 Automaton.rewrite w a >>= fun ts ->
 assert (List.mem w ts);
 assert (List.length ts = 1);

 (* function context TODO test optional flag c *)
 (*
 let printf t p cs =
  Format.printf "@\ncontext of ";
  Term.fprintfm Format.std_formatter t >>= fun _ ->
  Format.printf " -> %a:@\n" State.fprintf p;
  M.fprintf (fun fmt (t,p) ->
   Term.fprintfm fmt t >>= fun _ ->
   M.return (Format.printf " -> %a" State.fprintf p))
   "@\n" Format.std_formatter cs
 in

 automaton:
 
 a -> 3,2,1
 b -> 4
 c -> 3
 f(1,4) -> 2
 f(2,1) -> 5,4
 g(2) -> 3
 g(4) -> 3,1
 i(1,4,2) -> 3
 2 -> 4
 3 -> 2
 
 term i(b,f(c,f(a,3)),g(a)):

 b -> 1, f(c,f(a,3)) -> 4, g(a) -> 2
 b -> 1, c -> 1, f(a,3) -> 4, g(a) -> 2 => b -> 1, c -> 1
 b -> 1, c -> 2, f(a,3) -> 1, g(a) -> 2 => b -> 1, f(a,3) -> 1

 term f(g(b),g(6)):

 g(b) -> 1, g(6) -> 4 => g(6) -> 4
 g(b) -> 2, g(6) -> 1 => g(6) -> 1

 term f(g(b),b):

 g(b) -> 1, b -> 4 => -
 g(b) -> 2, b -> 1 => b -> 1

 term i(b,f(2,c),b):
 
 b -> 1, f(2,c) -> 4, b -> 2
 b -> 1, c -> 1, b -> 2

 term i(b,f(b,4),b):

 b -> 1, f(b,4) -> 4, b -> 2
 b -> 1, b -> 2
 *)

 Term.of_string vs ps "i(b,f(c,f(a,3)),g(a))" >>= fun s ->
 Term.of_string vs ps "f(g(b),g(6))" >>= fun t ->
 Term.of_string vs ps "f(g(b),b)" >>= fun u ->
 Term.of_string vs ps "i(b,f(2,c),b)" >>= fun v ->
 Term.of_string vs ps "i(b,f(b,4),b)" >>= fun w ->

 Automaton.context s p3 e >>= fun cs ->
 assert (List.mem (s,p3) cs);
 assert (List.length cs = 1);

 Automaton.context t p4 e >>= fun cs ->
 Term.of_string vs ps "g(6)" >>= fun x ->
 assert (List.mem (x,p1) cs);
 assert (List.length cs = 1);

 Automaton.context u p4 e >>= fun cs ->
 Term.of_string vs ps "b" >>= fun x ->
 assert (List.length cs = 0);

 Automaton.context u p5 e >>= fun cs ->
 Term.of_string vs ps "b" >>= fun x ->
 assert (List.mem (x,p1) cs);
 assert (List.length cs = 1);

 Automaton.context v p3 e >>= fun cs ->
 assert (List.mem (v,p3) cs);
 assert (List.length cs = 1);

 Automaton.context w p3 e >>= fun cs ->
 assert (List.mem (w,p3) cs);
 assert (List.length cs = 1);

 Automaton.context ~n:2 s p3 e >>= fun cs ->
 Term.of_string vs ps "b" >>= fun x ->
 assert (List.mem (x,p1) cs);
 Term.of_string vs ps "c" >>= fun x ->
 assert (List.mem (x,p1) cs);
 assert (List.length cs = 2);

 Automaton.context ~n:2 t p4 e >>= fun cs ->
 Term.of_string vs ps "g(6)" >>= fun x ->
 assert (List.mem (x,p1) cs);
 assert (List.length cs = 1);

 Automaton.context ~n:2 u p4 e >>= fun cs ->
 Term.of_string vs ps "b" >>= fun x ->
 assert (List.length cs = 0);

 Automaton.context ~n:2 u p5 e >>= fun cs ->
 Term.of_string vs ps "b" >>= fun x ->
 assert (List.mem (x,p1) cs);
 assert (List.length cs = 1);

 Automaton.context ~n:2 v p3 e >>= fun cs ->
 assert (List.mem (v,p3) cs);
 assert (List.length cs = 1);

 Automaton.context ~n:2 w p3 e >>= fun cs ->
 assert (List.mem (w,p3) cs);
 assert (List.length cs = 1);

 Automaton.context ~n:3 s p3 e >>= fun cs ->
 Term.of_string vs ps "b" >>= fun x ->
 assert (List.mem (x,p1) cs);
 Term.of_string vs ps "c" >>= fun x ->
 assert (List.mem (x,p1) cs);
 assert (List.length cs = 2);

 Automaton.context ~n:3 t p4 e >>= fun cs ->
 Term.of_string vs ps "g(6)" >>= fun x ->
 assert (List.mem (x,p1) cs);
 assert (List.length cs = 1);

 Automaton.context ~n:3 u p4 e >>= fun cs ->
 Term.of_string vs ps "b" >>= fun x ->
 assert (List.length cs = 0);

 Automaton.context ~n:3 u p5 e >>= fun cs ->
 Term.of_string vs ps "b" >>= fun x ->
 assert (List.mem (x,p1) cs);
 assert (List.length cs = 1);

 Automaton.context ~n:3 v p3 e >>= fun cs ->
 Term.of_string vs ps "b" >>= fun x ->
 assert (List.mem (x,p1) cs);
 assert (List.mem (x,p2) cs);
 Term.of_string vs ps "c" >>= fun x ->
 assert (List.mem (x,p1) cs);
 assert (List.length cs = 3);

 Automaton.context ~n:3 w p3 e >>= fun cs ->
 Term.of_string vs ps "b" >>= fun x ->
 assert (List.mem (x,p1) cs);
 assert (List.mem (x,p2) cs);
 assert (List.length cs = 2);

 (* function compatible TODO test optional flag c *)
 let i =
  "f(x,f(a,x)) -> p(x) \
   f(a,g(b)) -> s(c) \
   g(f(x,g(y))) -> h(x,y)"
 in
 M.get >>= fun (s,status) ->
 let (trs,s) = Either.right (R.eval s (Trs.of_string vs i)) in
 M.set (s,status) >>
 let i =
  "f(x,f(a,x)) -> p(x) \
   f(x,f(a,y)) -> p(y) \
   g(f(x,g(y))) -> h(x,y)"
 in
 M.get >>= fun (s,status) ->
 let (trs',s) = Either.right (R.eval s (Trs.of_string vs i)) in
 M.set (s,status) >>
 let i = "f(a,x) -> g(x)" in
 M.get >>= fun (s,status) ->
 let (trs'',s) = Either.right (R.eval s (Trs.of_string vs i)) in
 M.set (s,status) >>
 let i =
  "g(c) -> f(c,c) \
   c -> a"
 in
 M.get >>= fun (s,status) ->
 let (trs''',s) = Either.right (R.eval s (Trs.of_string vs i)) in
 M.set (s,status) >>

 (*
 let printf vs =
  Format.printf "@\nviolations:@\n";
  M.fprintf (fun fmt (r,p) ->
   Term.fprintfm fmt r >>= fun _ ->
   M.return (Format.fprintf fmt " -> %a" State.fprintf p))
   "@\n" Format.std_formatter vs >>= fun _ ->
  M.return (Format.printf "@\n")
 in

 a -> 1,2,3
 b -> 4
 c -> 3
 f(1,4) -> 2
 f(2,1) -> 4,5
 g(2) -> 3
 g(4) -> 1,3
 3 -> 2
 2 -> 4

 trs: f(x,f(a,x)) -> p(x)
      f(a,g(b)) -> s(c)
      g(f(x,g(y))) -> h(x,y)

 rule f(x,f(a,x)) -> p(x):
 
 f(1,f(a,1)) -> 2 => p(1) -> 2
 with history: -
 
 rule f(a,g(b)) -> s(c):
 
 f(a,g(b)) -> 2,4,5 => s(c) -> 2,4,5
 with history: s(c) -> 2
 
 rule g(f(x,g(y))) -> h(x,y):
 
 g(f(1,g(2))) -> 1,3 => h(1,2) -> 1,3
 g(f(1,g(4))) -> 1,3 => h(1,4) -> 1,3
 g(f(2,g(4))) -> 1,3 => h(2,4) -> 1,3
 with history: h(1,2) -> 1,3
               h(1,4) -> 3

 trs: f(x,f(a,x)) -> p(x)
      f(x,f(a,y)) -> p(y)
      g(f(x,g(y))) -> h(x,y)

 rule f(x,f(a,y)) -> p(y):
 
 f(1,f(a,1)) -> 2 => p(1) -> 2
 f(1,f(a,4)) -> 2 => p(4) -> 2
 with history: p(4) -> 2

 a -> 1
 f(1,2) -> 2
 f(1,21) -> 2
 f(21,2) -> 2
 f(21,21) -> 2
 g(2) -> 1,2,21
 g(21) -> 21

 trs: f(a,x) -> g(x)

 f(a,2) -> 2 => -
 f(a,21) -> 2 => g(21) -> 2
 *)

 Automaton.compatible trs a >>= fun violations ->
 Term.of_string vs ps "p(1)" >>= fun x ->
 assert (List.mem (x,p2) violations);
 Term.of_string vs ps "s(c)" >>= fun x ->
 assert (List.mem (x,p2) violations);
 assert (List.mem (x,p4) violations);
 assert (List.mem (x,p5) violations);
 Term.of_string vs ps "h(1,2)" >>= fun x ->
 assert (List.mem (x,p1) violations);
 assert (List.mem (x,p3) violations);
 Term.of_string vs ps "h(1,4)" >>= fun x ->
 assert (List.mem (x,p1) violations);
 assert (List.mem (x,p3) violations);
 Term.of_string vs ps "h(2,4)" >>= fun x ->
 assert (List.mem (x,p1) violations);
 assert (List.mem (x,p3) violations);
 assert (List.length violations = 10);

 Automaton.compatible trs' a >>= fun violations ->
 Term.of_string vs ps "p(1)" >>= fun x ->
 assert (List.mem (x,p2) violations);
 Term.of_string vs ps "p(4)" >>= fun x ->
 assert (List.mem (x,p2) violations);
 Term.of_string vs ps "h(1,2)" >>= fun x ->
 assert (List.mem (x,p1) violations);
 assert (List.mem (x,p3) violations);
 Term.of_string vs ps "h(1,4)" >>= fun x ->
 assert (List.mem (x,p1) violations);
 assert (List.mem (x,p3) violations);
 Term.of_string vs ps "h(2,4)" >>= fun x ->
 assert (List.mem (x,p1) violations);
 assert (List.mem (x,p3) violations);
 assert (List.length violations = 8);

 Automaton.quasi_det (Automaton.copy f) >>= fun f' ->
 Automaton.compatible trs'' f' >>= fun violations ->
 Term.of_string vs ["21"] "g(21)" >>= fun x ->
 assert (List.mem (x,p2) violations);
 assert (List.length violations = 1);

 Automaton.compatible trs''' a >>= fun violations ->
 Term.of_string vs ps "f(c,c)" >>= fun x ->
 assert (List.mem (x,p1) violations);
 assert (List.mem (x,p3) violations);

 Automaton.compatible ~h:(Some h) trs a >>= fun violations ->
 Term.of_string vs ps "s(c)" >>= fun x ->
 assert (List.mem (x,p2) violations);
 Term.of_string vs ps "h(1,2)" >>= fun x ->
 assert (List.mem (x,p1) violations);
 assert (List.mem (x,p3) violations);
 Term.of_string vs ps "h(1,4)" >>= fun x ->
 assert (List.mem (x,p3) violations);
 assert (List.length violations = 4);

 Automaton.compatible ~h:(Some h) trs' a >>= fun violations ->
 Term.of_string vs ps "p(4)" >>= fun x ->
 assert (List.mem (x,p2) violations);
 Term.of_string vs ps "h(1,2)" >>= fun x ->
 assert (List.mem (x,p1) violations);
 assert (List.mem (x,p3) violations);
 Term.of_string vs ps "h(1,4)" >>= fun x ->
 assert (List.mem (x,p3) violations);
 assert (List.length violations = 4);

 (* function quasi_det *)
 (*
 start:
 a -> 1,2,3
 b -> 4
 c -> 3
 f(1,4) -> 2
 f(2,1) -> 4,5
 g(2) -> 3
 g(4) -> 1,3
 3 -> 2
 2 -> 4
 
 ec:
 a -> 1,2,3,4
 b -> 4
 c -> 3,2,4
 f(1,4) -> 2,4
 f(2,1) -> 4,5
 g(2) -> 3,2,4
 g(4) -> 1,3,2,4
 3 -> 2
 2 -> 4
 
 init:
 a -> {1,2,3,4}
 b -> 4
 c -> {3,2,4}
 f(1,4) -> {2,4}
 f(2,1) -> {4,5}
 g(2) -> {3,2,4}
 g(4) -> {1,3,2,4}
 3 -> 2
 2 -> 4
 
 step 1:
 1 -> {1,2,3,4}
 2 -> {1,2,3,4},{2,3,4},{2,4}
 4 -> {1,2,3,4},{2,3,4},{2,4},{4,5}
 
 a -> {1,2,3,4}
 b -> 4
 c -> {3,2,4}
 f(1,4) -> {2,4}
 f(1,{1,2,3,4}) -> {2,4}
 f(1,{2,3,4}) -> {2,4}
 f(1,{2,4}) -> {2,4}
 f(1,{4,5}) -> {2,4}
 f({1,2,3,4},4) -> {2,4}
 f({1,2,3,4},{1,2,3,4}) -> {2,4},{4,5} = {2,4,5}
 f({1,2,3,4},{2,3,4}) -> {2,4}
 f({1,2,3,4},{2,4}) -> {2,4}
 f({1,2,3,4},{4,5}) -> {2,4}
 f(2,1) -> {4,5}
 f({1,2,3,4},1) -> {4,5}
 f({2,3,4},1) -> {4,5}
 f({2,4},1) -> {4,5}
 f(2,{1,2,3,4}) -> {4,5}
 f({2,3,4},{1,2,3,4}) -> {4,5}
 f({2,4},{1,2,3,4}) -> {4,5}
 g(2) -> {3,2,4}
 g({1,2,3,4}) -> {1,3,2,4},{3,2,4} = {1,2,3,4}
 g({2,3,4}) -> {1,3,2,4},{3,2,4} = {1,2,3,4}
 g({2,4}) -> {1,3,2,4},{3,2,4} = {1,2,3,4}
 g(4) -> {1,3,2,4}
 g({4,5}) -> {1,3,2,4}
 3 -> 2
 2 -> 4
 
 step 2:
 {2,4} -> {2,4,5}
 {4,5} -> {2,4,5}
 
 a -> {1,2,3,4}
 b -> 4
 c -> {3,2,4}
 f(1,4) -> {2,4}
 f(1,{1,2,3,4}) -> {2,4}
 f(1,{2,3,4}) -> {2,4}
 f(1,{2,4}) -> {2,4}
 f(1,{2,4,5}) -> {2,4}
 f(1,{4,5}) -> {2,4}
 f({1,2,3,4},1) -> {4,5}
 f({1,2,3,4},4) -> {2,4}
 f({1,2,3,4},{1,2,3,4}) -> {2,4,5}
 f({1,2,3,4},{2,3,4}) -> {2,4}
 f({1,2,3,4},{2,4}) -> {2,4}
 f({1,2,3,4},{2,4,5}) -> {2,4}
 f({1,2,3,4},{4,5}) -> {2,4}
 f(2,1) -> {4,5}
 f(2,{1,2,3,4}) -> {4,5}
 f({2,4},{1,2,3,4}) -> {4,5}
 f({2,4},1) -> {4,5}
 f({2,3,4},1) -> {4,5}
 f({2,3,4},{1,2,3,4}) -> {4,5}
 f({2,4,5},1) -> {4,5}
 f({2,4,5},{1,2,3,4}) -> {4,5}
 g(2) -> {3,2,4}
 g(4) -> {1,3,2,4}
 g({1,2,3,4}) -> {1,2,3,4}
 g({2,3,4}) -> {1,2,3,4}
 g({2,4}) -> {1,2,3,4}
 g({2,4,5}) -> {1,2,3,4}
 g({4,5}) -> {1,3,2,4}
 3 -> 2
 2 -> 4
 
 final:
 
 a -> 1,2,3,4,{1,2,3,4}
 b -> 4
 c -> 2,3,4,{3,2,4}
 f(1,4) -> 2,4,{2,4}
 f(1,{1,2,3,4}) -> {2,4}
 f(1,{2,3,4}) -> {2,4}
 f(1,{2,4}) -> {2,4}
 f(1,{2,4,5}) -> {2,4}
 f(1,{4,5}) -> {2,4}
 f({1,2,3,4},1) -> {4,5}
 f({1,2,3,4},4) -> {2,4}
 f({1,2,3,4},{1,2,3,4}) -> {2,4,5}
 f({1,2,3,4},{2,3,4}) -> {2,4}
 f({1,2,3,4},{2,4}) -> {2,4}
 f({1,2,3,4},{2,4,5}) -> {2,4}
 f({1,2,3,4},{4,5}) -> {2,4}
 f(2,1) -> 4,5,{4,5}
 f(2,{1,2,3,4}) -> {4,5}
 f({2,4},{1,2,3,4}) -> {4,5}
 f({2,4},1) -> {4,5}
 f({2,3,4},1) -> {4,5}
 f({2,3,4},{1,2,3,4}) -> {4,5}
 f({2,4,5},1) -> {4,5}
 f({2,4,5},{1,2,3,4}) -> {4,5}
 g(2) -> 2,3,4,{3,2,4}
 g(4) -> 1,2,3,4,{1,3,2,4}
 g({1,2,3,4}) -> {1,2,3,4}
 g({2,3,4}) -> {1,2,3,4}
 g({2,4}) -> {1,2,3,4}
 g({2,4,5}) -> {1,2,3,4}
 g({4,5}) -> {1,3,2,4}
 3 -> 2
 2 -> 4

 completely defined:

 a -> 1
 f(1,1) -> {}
 f(1,2) -> 2
 f(1,{1,2}) -> 2
 f(2,1) -> {}
 f(2,2) -> {}
 f(2,{1,2}) -> {}
 f({1,2},1) -> {}
 f({1,2},2) -> 2
 f({1,2},{1,2}) -> 2
 g(1) -> {}
 g(2) -> 1,2,{1,2}
 g({1,2}) -> {1,2}

 a -> 1,2,3,4,{1,2,3,4}
 b -> 4
 c -> 2,3,4,{3,2,4}
 f(1,4) -> 2,4,{2,4}
 f(1,{1,2,3,4}) -> {2,4}
 f(1,{2,3,4}) -> {2,4}
 f(1,{2,4}) -> {2,4}
 f(1,{2,4,5}) -> {2,4}
 f(1,{4,5}) -> {2,4}

 f({1,2,3,4},1) -> {4,5}
 f({1,2,3,4},4) -> {2,4}
 f({1,2,3,4},{1,2,3,4}) -> {2,4,5}
 f({1,2,3,4},{2,3,4}) -> {2,4}
 f({1,2,3,4},{2,4}) -> {2,4}
 f({1,2,3,4},{2,4,5}) -> {2,4}
 f({1,2,3,4},{4,5}) -> {2,4}
 f(2,1) -> 4,5,{4,5}
 f(2,{1,2,3,4}) -> {4,5}
 f({2,4},{1,2,3,4}) -> {4,5}
 f({2,4},1) -> {4,5}
 f({2,3,4},1) -> {4,5}
 f({2,3,4},{1,2,3,4}) -> {4,5}
 f({2,4,5},1) -> {4,5}
 f({2,4,5},{1,2,3,4}) -> {4,5}
 g(2) -> 2,3,4,{3,2,4}
 g(4) -> 1,2,3,4,{1,3,2,4}
 g({1,2,3,4}) -> {1,2,3,4}
 g({2,3,4}) -> {1,2,3,4}
 g({2,4}) -> {1,2,3,4}
 g({2,4,5}) -> {1,2,3,4}
 g({4,5}) -> {1,3,2,4}
 3 -> 2
 2 -> 4
 *)

 M.get >>= fun (s,_) -> M.set (s,Status.init) >> M.create_state 15 >>
 Automaton.quasi_det (Automaton.copy a) >>= fun a' ->
 assert (Automaton.size a' = 51);
 assert (List.length (Automaton.finals a') = 3);
 Lhs.of_string ps "f(16,16)" >>= fun l ->
 Automaton.update l p4 a' >>= fun a' ->
 Automaton.quasi_det a' >>= fun a' ->
 assert (Automaton.size a' = 52); 
 assert (List.length (Automaton.finals a') = 3);
 Automaton.update l p9 a' >>= fun a' ->
 Automaton.quasi_det a' >>= fun a' ->
 assert (Automaton.size a' = 59);
 assert (List.length (Automaton.finals a') = 3);
 Lhs.of_string ps "h(3,5)" >>= fun l ->
 Automaton.update l p2 a' >>= fun a' ->
 Automaton.quasi_det a' >>= fun a' ->
 assert (Automaton.size a' = 73);

 Automaton.quasi_det (Automaton.copy b) >>= fun b' ->
 assert (Automaton.size b' = 451);
 assert (List.length (Automaton.finals b') = 4);

 Automaton.quasi_det (Automaton.copy c) >>= fun c' ->
 assert (Automaton.size c' = 24);
 assert (List.length (Automaton.finals c') = 3);
 Lhs.of_string ps "f(37,35)" >>= fun l ->
 M.create_state 35 >>= fun p ->
 Automaton.update l p c' >>= fun c' ->
 Lhs.of_string ps "f(8,35)" >>= fun l ->
 Automaton.update l p10 c' >>= fun c' ->
 Automaton.quasi_det c' >>= fun c' ->
 assert (Automaton.size c' = 27);
 assert (List.length (Automaton.finals c') = 3);

 M.get >>= fun (state,status) ->
 Automaton.quasi_det ~c:true (Automaton.copy f) >>= fun f' ->
 assert (Automaton.size f' = 15);
 assert (List.length (Automaton.finals ~i:true f') = 2);

 Automaton.quasi_det ~c:true (Automaton.copy a) >>= fun a' ->
 assert (Automaton.size a' = 1015);
 assert (List.length (Automaton.finals ~i:true a') = 3);
 M.set (state,status) >>

 (* function det *)
 (*
 final quasi-deterministic:
 
 a -> 1,2,3,4,{1,2,3,4}
 b -> 4
 c -> 2,3,4,{3,2,4}
 f(1,4) -> 2,4,{2,4}
 f(1,{1,2,3,4}) -> {2,4}
 f(1,{2,3,4}) -> {2,4}
 f(1,{2,4}) -> {2,4}
 f(1,{2,4,5}) -> {2,4}
 f(1,{4,5}) -> {2,4}
 f({1,2,3,4},1) -> {4,5}
 f({1,2,3,4},4) -> {2,4}
 f({1,2,3,4},{1,2,3,4}) -> {2,4,5}
 f({1,2,3,4},{2,3,4}) -> {2,4}
 f({1,2,3,4},{2,4}) -> {2,4}
 f({1,2,3,4},{2,4,5}) -> {2,4}
 f({1,2,3,4},{4,5}) -> {2,4}
 f(2,1) -> 4,5,{4,5}
 f(2,{1,2,3,4}) -> {4,5}
 f({2,4},{1,2,3,4}) -> {4,5}
 f({2,4},1) -> {4,5}
 f({2,3,4},1) -> {4,5}
 f({2,3,4},{1,2,3,4}) -> {4,5}
 f({2,4,5},1) -> {4,5}
 f({2,4,5},{1,2,3,4}) -> {4,5}
 g(2) -> 2,3,4,{3,2,4}
 g(4) -> 1,2,3,4,{1,3,2,4}
 g({1,2,3,4}) -> {1,2,3,4}
 g({2,3,4}) -> {1,2,3,4}
 g({2,4}) -> {1,2,3,4}
 g({2,4,5}) -> {1,2,3,4}
 g({4,5}) -> {1,3,2,4}
 3 -> 2
 2 -> 4
 
 final:
 
 a -> {1,2,3,4}
 b -> 4
 c -> {3,2,4}
 f(1,4) -> {2,4}
 f(1,{1,2,3,4}) -> {2,4}
 f(1,{2,3,4}) -> {2,4}
 f(1,{2,4}) -> {2,4}
 f(1,{2,4,5}) -> {2,4}
 f(1,{4,5}) -> {2,4}
 f({1,2,3,4},1) -> {4,5}
 f({1,2,3,4},4) -> {2,4}
 f({1,2,3,4},{1,2,3,4}) -> {2,4,5}
 f({1,2,3,4},{2,3,4}) -> {2,4}
 f({1,2,3,4},{2,4}) -> {2,4}
 f({1,2,3,4},{2,4,5}) -> {2,4}
 f({1,2,3,4},{4,5}) -> {2,4}
 f(2,1) -> {4,5}
 f(2,{1,2,3,4}) -> {4,5}
 f({2,4},{1,2,3,4}) -> {4,5}
 f({2,4},1) -> {4,5}
 f({2,3,4},1) -> {4,5}
 f({2,3,4},{1,2,3,4}) -> {4,5}
 f({2,4,5},1) -> {4,5}
 f({2,4,5},{1,2,3,4}) -> {4,5}
 g(2) -> {3,2,4}
 g(4) -> {1,3,2,4}
 g({1,2,3,4}) -> {1,2,3,4}
 g({2,3,4}) -> {1,2,3,4}
 g({2,4}) -> {1,2,3,4}
 g({2,4,5}) -> {1,2,3,4}
 g({4,5}) -> {1,3,2,4}
 *)

 Automaton.det (Automaton.copy a) >>= fun a' ->
 assert (Automaton.size a' = 31);
 assert (List.length (Automaton.finals a') = 2);
 Lhs.of_string ps "f(38,38)" >>= fun l ->
 Automaton.update l p4 a' >>= fun a' ->
 Automaton.det ~q:true a' >>= fun a' ->
 assert (Automaton.size a' = 31);
 assert (List.length (Automaton.finals a') = 2);
 Automaton.update l p9 a' >>= fun a' ->
 Automaton.det ~q:true a' >>= fun a' ->
 assert (Automaton.size a' = 36);
 assert (List.length (Automaton.finals a') = 2);

 Automaton.det (Automaton.copy b) >>= fun b' ->
 assert (Automaton.size b' = 424);
 assert (List.length (Automaton.finals b') = 4);

 Automaton.det (Automaton.copy c) >>= fun c' ->
 assert (Automaton.size c' = 20);
 assert (List.length (Automaton.finals c') = 3);
 Lhs.of_string ps "f(59,57)" >>= fun l ->
 M.create_state 57 >>= fun p ->
 Automaton.update l p c' >>= fun c' ->
 Lhs.of_string ps "f(8,57)" >>= fun l ->
 Automaton.update l p10 c' >>= fun c' ->
 Automaton.det ~q:true c' >>= fun c' ->
 assert (Automaton.size c' = 22);
 assert (List.length (Automaton.finals c') = 3);
 M.return ()
;;

Format.printf "testing module Automaton    ... ";;
ignore (M.run (S.empty 10,Status.init) test);;
Format.printf "ok@\n";;

(* Tests: Module Transducer *)
let test =
 M.create_state 1 >>= fun p1 -> M.create_state 2 >>= fun p2 ->
 M.create_state 3 >>= fun p3 -> M.create_state 4 >>= fun p4 ->
 M.create_state 5 >>= fun p5 -> M.create_state 6 >>= fun p6 ->
 M.create_state 7 >>= fun p7 -> M.create_state 8 >>= fun p8 ->
 M.create_state 9 >>= fun p9 -> M.create_state 10 >>= fun p10 ->
 M.create_state 11 >>= fun p11 -> M.create_state 12 >>= fun p12 ->
 M.create_state 13 >>= fun p13 -> M.create_state 14 >>= fun p14 ->
 M.create_state 15 >>= fun p15 -> M.create_state 16 >>= fun p16 ->
 M.create_state 17 >>= fun p17 -> M.create_state 18 >>= fun p18 ->
 M.create_state 19 >>= fun p19 -> M.create_state 20 >>= fun p20 ->
 M.get >>= fun (state,_) -> M.set (state,Status.add_state p15 Status.init) >>
 let ps = ["1";"2";"3";"4";"5";"6";"7";"8";"9";"10";"11";"12";"13";"14";"15"] in
 let s = 
  "a -> 1 \
   b -> 2 \
   c -> 3 \
   g(3) -> 4"
 in
 Automaton.of_string ps s >>= fun a ->
 let s = 
  "b -> 5 \
   c -> 2 \
   d -> 4 \
   g(5) -> 1"
 in
 Automaton.of_string ps s >>= fun b ->
 (*
 relation transducer t:    a -> 1 <- g(b)
                           b -> 2 <- c
                        g(c) -> 4 <- d
 *)
 let t = Transducer.make a b in
 let s = 
  "a -> 1 \
   a -> 2 \
   b -> 1 \
   b -> 3 \
   f(1,1) -> 1 \
   f(1,3) -> 5 \
   f(4,2) -> 6 \
   g(1) -> 1 \
   g(1) -> 4 \
   g(2) -> 7 \
   g(5) -> 8"
 in
 Automaton.of_string ps s >>= fun a ->
 let s = 
  "a -> 9
   b -> 9
   b -> 10
   f(9,9) -> 9
   f(12,9) -> 6
   g(9) -> 9
   g(9) -> 11
   g(10) -> 7
   g(11) -> 12
   9 -> 8"
 in
 Automaton.of_string ps s >>= fun b ->
 (*
 relation transducer u: f(g(x),a) -> 6 <- f(g(g(y)),z)
                             g(a) -> 7 <- g(b)
                        g(f(x,b)) -> 8 <- y
 *)
 let u = Transducer.make a b in

 (* function invert *)
 assert (Transducer.fst (Transducer.invert t) = Transducer.snd t);
 assert (Transducer.snd (Transducer.invert t) = Transducer.fst t);
 assert (Transducer.invert (Transducer.invert t) = t);

 assert (Transducer.fst (Transducer.invert u) = Transducer.snd u);
 assert (Transducer.snd (Transducer.invert u) = Transducer.fst u);
 assert (Transducer.invert (Transducer.invert u) = u);

 (* function transitive_closure *)
 (*
 transitive closure t: a <-> g(b), b <-> c, g(c) <-> d
                       a <-> g(c), a <-> d, g(b) <-> d

 first: a -> 1            second: b -> 5
        b -> 2                    c -> 2
        c -> 3                    d -> 4
        g(3) -> 4                 g(5) -> 1
        1 -> 4                    2 -> 5
        2 -> 3                    4 -> 1

 transitive closure u: f(g(x),a) <-> f(g(g(y)),z)
                            g(a) <-> g(b)
                       g(f(x,b)) <-> y
                                 ...

 first: a -> 1,2            second: a -> 9
        b -> 1,3                    b -> 9,10
        f(1,1) -> 1                 f(9,9) -> 9
        f(1,3) -> 5                 f(12,9) -> 6
        f(4,2) -> 6                 g(9) -> 9,11
        g(1) -> 1,4                 g(10) -> 7
        g(2) -> 7                   g(11) -> 12
        g(5) -> 8                   9 -> 8
        6 -> 1,5                    6 -> 8,9,11,12
        7 -> 1,4                    7 -> 8,9,11,12
        8 -> 1,2,3,4,5,6,7          8 -> 9,11,12
 *)
 Transducer.transitive_closure (Transducer.copy t) >>= fun t' ->
 let a = Transducer.fst t' and b = Transducer.snd t' in
 Lhs.of_string ps "a" >>= fun l -> Automaton.find l a >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l a >>= fun r ->
 assert (Rhs.mem p2 (Option.the r));
 Lhs.of_string ps "c" >>= fun l -> Automaton.find l a >>= fun r ->
 assert (Rhs.mem p3 (Option.the r));
 Lhs.of_string ps "g(3)" >>= fun l -> Automaton.find l a >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 Lhs.of_string ps "1" >>= fun l -> Automaton.find l a >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 Lhs.of_string ps "2" >>= fun l -> Automaton.find l a >>= fun r ->
 assert (Rhs.mem p3 (Option.the r));
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l b >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 Lhs.of_string ps "c" >>= fun l -> Automaton.find l b >>= fun r ->
 assert (Rhs.mem p2 (Option.the r));
 Lhs.of_string ps "d" >>= fun l -> Automaton.find l b >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 Lhs.of_string ps "g(5)" >>= fun l -> Automaton.find l b >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 Lhs.of_string ps "2" >>= fun l -> Automaton.find l b >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 Lhs.of_string ps "4" >>= fun l -> Automaton.find l b >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Transducer.size t' = 12);

 Transducer.transitive_closure (Transducer.copy u) >>= fun u' ->
 let a = Transducer.fst u' and b = Transducer.snd u' in
 Lhs.of_string ps "a" >>= fun l -> Automaton.find l a >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p2 (Option.the r));
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l a >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p3 (Option.the r));
 Lhs.of_string ps "f(1,1)" >>= fun l -> Automaton.find l a >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 Lhs.of_string ps "f(1,3)" >>= fun l -> Automaton.find l a >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 Lhs.of_string ps "f(4,2)" >>= fun l -> Automaton.find l a >>= fun r ->
 assert (Rhs.mem p6 (Option.the r));
 Lhs.of_string ps "g(1)" >>= fun l -> Automaton.find l a >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p4 (Option.the r));
 Lhs.of_string ps "g(2)" >>= fun l -> Automaton.find l a >>= fun r ->
 assert (Rhs.mem p7 (Option.the r));
 Lhs.of_string ps "g(5)" >>= fun l -> Automaton.find l a >>= fun r ->
 assert (Rhs.mem p8 (Option.the r));
 Lhs.of_string ps "6" >>= fun l -> Automaton.find l a >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p5 (Option.the r));
 Lhs.of_string ps "7" >>= fun l -> Automaton.find l a >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p4 (Option.the r));
 Lhs.of_string ps "8" >>= fun l -> Automaton.find l a >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p2 (Option.the r));
 assert (Rhs.mem p3 (Option.the r));
 assert (Rhs.mem p4 (Option.the r));
 assert (Rhs.mem p5 (Option.the r));
 assert (Rhs.mem p6 (Option.the r));
 assert (Rhs.mem p7 (Option.the r));
 Lhs.of_string ps "a" >>= fun l -> Automaton.find l b >>= fun r ->
 assert (Rhs.mem p9 (Option.the r));
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l b >>= fun r ->
 assert (Rhs.mem p9 (Option.the r));
 assert (Rhs.mem p10 (Option.the r));
 Lhs.of_string ps "f(9,9)" >>= fun l -> Automaton.find l b >>= fun r ->
 assert (Rhs.mem p9 (Option.the r));
 Lhs.of_string ps "f(12,9)" >>= fun l -> Automaton.find l b >>= fun r ->
 assert (Rhs.mem p6 (Option.the r));
 Lhs.of_string ps "g(9)" >>= fun l -> Automaton.find l b >>= fun r ->
 assert (Rhs.mem p9 (Option.the r));
 assert (Rhs.mem p11 (Option.the r));
 Lhs.of_string ps "g(10)" >>= fun l -> Automaton.find l b >>= fun r ->
 assert (Rhs.mem p7 (Option.the r));
 Lhs.of_string ps "g(11)" >>= fun l -> Automaton.find l b >>= fun r ->
 assert (Rhs.mem p12 (Option.the r));
 Lhs.of_string ps "6" >>= fun l -> Automaton.find l b >>= fun r ->
 assert (Rhs.mem p8 (Option.the r));
 assert (Rhs.mem p9 (Option.the r));
 assert (Rhs.mem p11 (Option.the r));
 assert (Rhs.mem p12 (Option.the r));
 Lhs.of_string ps "7" >>= fun l -> Automaton.find l b >>= fun r ->
 assert (Rhs.mem p8 (Option.the r));
 assert (Rhs.mem p9 (Option.the r));
 assert (Rhs.mem p11 (Option.the r));
 assert (Rhs.mem p12 (Option.the r));
 Lhs.of_string ps "8" >>= fun l -> Automaton.find l b >>= fun r ->
 assert (Rhs.mem p9 (Option.the r));
 assert (Rhs.mem p11 (Option.the r));
 assert (Rhs.mem p12 (Option.the r));
 Lhs.of_string ps "9" >>= fun l -> Automaton.find l b >>= fun r ->
 assert (Rhs.mem p8 (Option.the r));
 assert (Transducer.size u' = 43);

 (* function successors *)
 (*
 t: a -> 1             b -> 5
    b -> 2             c -> 2
    c -> 3             d -> 4
    g(3) -> 4          g(5) -> 1
    1 -> 4             2 -> 5
    2 -> 3             4 -> 1

 successors: a -> 6,7
             b -> 5
             c -> 2
             d -> 4
             g(5) -> 1
             g(6) -> 6,8
             f(7,8) -> 9
             1 -> 6,7
             2 -> 5
             4 -> 1,6,7

 u: a -> 1,2                    a -> 9
    b -> 1,3                    b -> 9,10
    f(1,1) -> 1                 f(9,9) -> 9
    f(1,3) -> 5                 f(12,9) -> 6
    f(4,2) -> 6                 g(9) -> 9,11
    g(1) -> 1,4                 g(10) -> 7
    g(2) -> 7                   g(11) -> 12
    g(5) -> 8                   9 -> 8
    6 -> 1,5                    6 -> 8,9,11,12
    7 -> 1,4                    7 -> 8,9,11,12
    8 -> 1,2,3,4,5,6,7          8 -> 9,11,12

 successors: a -> 9,13
             b -> 9,10
             f(9,9) -> 9
             f(12,9) -> 6
             f(13,13) -> 13
             f(15,13) -> 16
             g(9) -> 9,11
             g(10) -> 7
             g(11) -> 12
             g(13) -> 13,14
             g(14) -> 15
             6 -> 8,9,11,12,13,14,15,16
             7 -> 8,9,11,12,13,14,15
             8 -> 9,11,12,13,14,15
             9 -> 8
 *)
 let s = 
  "a -> 6 \
   a -> 7 \
   g(6) -> 6 \
   g(6) -> 8 \
   f(7,8) -> 9"
 in
 Automaton.of_string ps s >>= fun a ->
 let a = Automaton.add_final p9 a in
 let s = 
  "a -> 13 \
   g(13) -> 13 \
   g(13) -> 14 \
   g(14) -> 15 \
   f(13,13) -> 13 \
   f(15,13) -> 16"
 in
 Automaton.of_string ps s >>= fun b ->
 let b = Automaton.add_final p16 b in

 Transducer.transitive_closure (Transducer.copy t) >>= fun t' ->
 Transducer.successors (Automaton.copy a) t' >>= fun a' ->
 Lhs.of_string ps "a" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p6 (Option.the r));
 assert (Rhs.mem p7 (Option.the r));
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 Lhs.of_string ps "c" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p2 (Option.the r));
 Lhs.of_string ps "d" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 Lhs.of_string ps "f(7,8)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p9 (Option.the r));
 Lhs.of_string ps "1" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p6 (Option.the r));
 assert (Rhs.mem p7 (Option.the r));
 Lhs.of_string ps "2" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 Lhs.of_string ps "4" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p6 (Option.the r));
 assert (Rhs.mem p7 (Option.the r));
 assert (Automaton.finals a' = [p9]);
 assert (Automaton.size a' = 15);

 Transducer.transitive_closure (Transducer.copy u) >>= fun u' ->
 Transducer.successors (Automaton.copy b) u' >>= fun b' ->
 Lhs.of_string ps "a" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p9 (Option.the r));
 assert (Rhs.mem p13 (Option.the r));
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p9 (Option.the r));
 assert (Rhs.mem p10 (Option.the r));
 Lhs.of_string ps "f(9,9)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p9 (Option.the r));
 Lhs.of_string ps "f(12,9)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p6 (Option.the r));
 Lhs.of_string ps "f(13,13)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p13 (Option.the r));
 Lhs.of_string ps "f(15,13)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p16 (Option.the r));
 Lhs.of_string ps "g(9)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p9 (Option.the r));
 assert (Rhs.mem p11 (Option.the r));
 Lhs.of_string ps "g(10)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p7 (Option.the r));
 Lhs.of_string ps "g(11)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p12 (Option.the r));
 Lhs.of_string ps "g(13)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p13 (Option.the r));
 assert (Rhs.mem p14 (Option.the r));
 Lhs.of_string ps "g(14)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p15 (Option.the r));
 Lhs.of_string ps "6" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p8 (Option.the r));
 assert (Rhs.mem p9 (Option.the r));
 assert (Rhs.mem p11 (Option.the r));
 assert (Rhs.mem p12 (Option.the r));
 assert (Rhs.mem p13 (Option.the r));
 assert (Rhs.mem p14 (Option.the r));
 assert (Rhs.mem p15 (Option.the r));
 assert (Rhs.mem p16 (Option.the r));
 Lhs.of_string ps "7" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p8 (Option.the r));
 assert (Rhs.mem p9 (Option.the r));
 assert (Rhs.mem p11 (Option.the r));
 assert (Rhs.mem p12 (Option.the r));
 assert (Rhs.mem p13 (Option.the r));
 assert (Rhs.mem p14 (Option.the r));
 assert (Rhs.mem p15 (Option.the r));
 Lhs.of_string ps "8" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p9 (Option.the r));
 assert (Rhs.mem p11 (Option.the r));
 assert (Rhs.mem p12 (Option.the r));
 assert (Rhs.mem p13 (Option.the r));
 assert (Rhs.mem p14 (Option.the r));
 assert (Rhs.mem p15 (Option.the r));
 Lhs.of_string ps "9" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p8 (Option.the r));
 assert (Automaton.finals b' = [p16]);
 assert (Automaton.size b' = 37);
 M.return ()
;;

Format.printf "testing module Transducer   ... ";;
ignore (M.run (S.empty 10,Status.init) test);;
Format.printf "ok@\n";;

(* Tests: Module Path *)
let test =
 M.create_state 1 >>= fun p1 -> M.create_state 2 >>= fun p2 ->
 M.create_state 3 >>= fun p3 -> M.create_state 4 >>= fun p4 ->
 M.create_state 5 >>= fun p5 -> M.create_state 6 >>= fun p6 ->
 M.create_state 7 >>= fun p7 -> M.create_state 8 >>= fun p8 ->
 M.create_state 9 >>= fun p9 -> M.create_state 10 >>= fun p10 ->
 M.create_state 11 >>= fun p11 -> M.create_state 12 >>= fun p12 ->
 M.create_state 13 >>= fun p13 -> M.create_state 14 >>= fun p14 ->
 M.create_state 15 >>= fun p15 ->
 let ps = ["1";"2";"3";"4";"5";"6";"7";"8";"9";"10";"11";"12";"13";"14";"15"] in
 let s = 
  "a -> 1 \
   a -> 2 \
   a -> 3 \
   b -> 4 \
   f(1,4) -> 2 \
   f(2,1) -> 4 \
   f(2,1) -> 5 \
   g(2) -> 3 \
   g(4) -> 1 \
   g(4) -> 3 \
   i(1,4,2) -> 3 \
   3 -> 2 \
   2 -> 4"
 in
 Automaton.of_string ps s >>= fun a ->
 let a = Automaton.add_final p3 a in
 
 (* functions fresh_min, fresh_funs, fresh_reuse, fresh_max
    TODO test optional flag c *)
 let vs = ["x";"y";"z"] in
 Term.of_string vs ps "g(f(1,h(b,3)))" >>= fun s ->
 Term.of_string vs ps "g(h(1,f(1,b)))" >>= fun t ->

 M.get >>= fun (state,_) -> M.set (state,Status.init) >> M.create_state 5 >>
 Path.fresh_min s p5 (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p6 (Option.the r));
 Lhs.of_string ps "h(6,3)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p6 (Option.the r));
 Lhs.of_string ps "f(1,6)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p6 (Option.the r));
 Lhs.of_string ps "g(6)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 assert (Automaton.size a' = 17);

 M.create_fun 2 "f" >>= fun f -> M.create_fun 1 "g" >>= fun g ->
 let fresh h = List.mem h [f;g] in
 Path.fresh_funs fresh s p5 (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p7 (Option.the r));
 Lhs.of_string ps "h(7,3)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p7 (Option.the r));
 Lhs.of_string ps "f(1,7)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p8 (Option.the r));
 Lhs.of_string ps "g(8)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 assert (Automaton.size a' = 17);

 Path.fresh_reuse s p5 (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "h(4,3)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p9 (Option.the r));
 Lhs.of_string ps "f(1,9)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p10 (Option.the r));
 Lhs.of_string ps "g(10)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 assert (Automaton.size a' = 16);

 Path.fresh_max s p5 (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p11 (Option.the r));
 Lhs.of_string ps "h(11,3)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p12 (Option.the r));
 Lhs.of_string ps "f(1,12)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p13 (Option.the r));
 Lhs.of_string ps "g(13)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 assert (Automaton.size a' = 17);

 M.get >>= fun (state,_) -> M.set (state,Status.init) >> M.create_state 5 >>
 Path.fresh_min t p5 (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p6 (Option.the r));
 Lhs.of_string ps "f(1,6)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p6 (Option.the r));
 Lhs.of_string ps "h(1,6)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p6 (Option.the r));
 Lhs.of_string ps "g(6)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 assert (Automaton.size a' = 17);

 M.create_fun 2 "f" >>= fun f -> M.create_fun 1 "g" >>= fun g ->
 let fresh h = List.mem h [f;g] in
 Path.fresh_funs fresh t p5 (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p7 (Option.the r));
 Lhs.of_string ps "f(1,7)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p8 (Option.the r));
 Lhs.of_string ps "h(1,8)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p7 (Option.the r));
 Lhs.of_string ps "g(7)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 assert (Automaton.size a' = 17);

 Path.fresh_reuse t p5 (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "h(1,2)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p9 (Option.the r));
 Lhs.of_string ps "g(9)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 assert (Automaton.size a' = 15);

 Path.fresh_max t p5 (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p10 (Option.the r));
 Lhs.of_string ps "f(1,10)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p11 (Option.the r));
 Lhs.of_string ps "h(1,11)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p12 (Option.the r));
 Lhs.of_string ps "g(12)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 assert (Automaton.size a' = 17);

 M.get >>= fun (state,_) -> M.set (state,Status.init) >> M.create_state 5 >>
 Path.fresh_min ~l:true t p5 (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p6 (Option.the r));
 Lhs.of_string ps "1" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p7 (Option.the r));
 assert (Rhs.mem p8 (Option.the r));
 Lhs.of_string ps "f(7,6)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p6 (Option.the r));
 Lhs.of_string ps "h(8,6)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p6 (Option.the r));
 Lhs.of_string ps "g(6)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p9 (Option.the r));
 Lhs.of_string ps "9" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 assert (Automaton.size a' = 20);

 M.get >>= fun (state,_) -> M.set (state,Status.init) >> M.create_state 5 >>
 M.create_fun 2 "f" >>= fun f -> M.create_fun 1 "g" >>= fun g ->
 let fresh h = List.mem h [f;g] in
 Path.fresh_funs ~l:true fresh t p5 (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p6 (Option.the r));
 Lhs.of_string ps "1" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p7 (Option.the r));
 assert (Rhs.mem p9 (Option.the r));
 Lhs.of_string ps "f(7,6)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p8 (Option.the r));
 Lhs.of_string ps "h(9,8)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p6 (Option.the r));
 Lhs.of_string ps "g(6)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p10 (Option.the r));
 Lhs.of_string ps "10" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 assert (Automaton.size a' = 20);

 M.get >>= fun (state,_) -> M.set (state,Status.init) >> M.create_state 5 >>
 Path.fresh_reuse ~l:true t p5 (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "1" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p6 (Option.the r));
 assert (Rhs.mem p8 (Option.the r));
 Lhs.of_string ps "f(6,4)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p7 (Option.the r));
 Lhs.of_string ps "h(8,7)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p9 (Option.the r));
 Lhs.of_string ps "g(9)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p10 (Option.the r));
 Lhs.of_string ps "10" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 assert (Automaton.size a' = 19);

 M.get >>= fun (state,_) -> M.set (state,Status.init) >> M.create_state 5 >>
 Path.fresh_max ~l:true t p5 (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p6 (Option.the r));
 Lhs.of_string ps "1" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p7 (Option.the r));
 assert (Rhs.mem p9 (Option.the r));
 Lhs.of_string ps "f(7,6)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p8 (Option.the r));
 Lhs.of_string ps "h(9,8)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p10 (Option.the r));
 Lhs.of_string ps "g(10)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p11 (Option.the r));
 Lhs.of_string ps "11" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 assert (Automaton.size a' = 20);

 (* functions torpa, suffix, tttbox, ttt2 TODO test optional flag c *)
 Term.of_string vs ps "f(g(b),g(f(1,3)))" >>= fun s ->
 Term.of_string vs ps "f(g(c),f(g(4),1))" >>= fun t ->
 let fresh = Path.fresh_max ~l:false in

 M.get >>= fun (state,_) -> M.set (state,Status.init) >> M.create_state 5 >>
 Path.torpa fresh s p5 (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "2" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 assert (Automaton.size a' = 14);

 Path.suffix fresh s p5 (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "2" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 assert (Automaton.size a' = 14);

 Path.suffix ~p:true fresh s p5 (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "f(1,1)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 assert (Automaton.size a' = 14);

 Path.tttbox fresh s p5 (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "2" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 assert (Automaton.size a' = 14);

 Path.tttbox ~p:true fresh s p5 (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "f(1,1)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 assert (Automaton.size a' = 14);

 Path.ttt2 fresh s p5 (Automaton.copy a) >>= fun a' ->
 assert (Automaton.size a' = 13);

 Path.ttt2 ~p:true fresh s p5 (Automaton.copy a) >>= fun a' ->
 assert (Automaton.size a' = 13);

 M.get >>= fun (state,_) -> M.set (state,Status.init) >> M.create_state 5 >>
 Path.torpa fresh t p5 (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "g(4)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p6 (Option.the r));
 Lhs.of_string ps "f(6,1)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p7 (Option.the r));
 Lhs.of_string ps "c" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p8 (Option.the r));
 Lhs.of_string ps "g(8)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p9 (Option.the r));
 Lhs.of_string ps "f(9,7)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 assert (Automaton.size a' = 18);

 M.get >>= fun (state,_) -> M.set (state,Status.init) >> M.create_state 5 >>
 Path.suffix fresh t p5 (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "c" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p6 (Option.the r));
 Lhs.of_string ps "g(6)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p7 (Option.the r));
 Lhs.of_string ps "f(7,4)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 assert (Automaton.size a' = 16);

 M.get >>= fun (state,_) -> M.set (state,Status.init) >> M.create_state 5 >>
 Path.suffix ~p:true fresh t p5 (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "c" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p6 (Option.the r));
 Lhs.of_string ps "g(6)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p7 (Option.the r));
 Lhs.of_string ps "f(7,4)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p5 (Option.the r));
 assert (Automaton.size a' = 16);

 M.get >>= fun (state,_) -> M.set (state,Status.init) >> M.create_state 5 >>
 Path.tttbox fresh t p4 (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "c" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 assert (Automaton.size a' = 14);

 M.get >>= fun (state,_) -> M.set (state,Status.init) >> M.create_state 5 >>
 Path.tttbox ~p:true fresh t p4 (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "c" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 assert (Automaton.size a' = 14);

 M.get >>= fun (state,_) -> M.set (state,Status.init) >> M.create_state 5 >>
 Path.ttt2 fresh t p4 (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "c" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 assert (Automaton.size a' = 14);

 M.get >>= fun (state,_) -> M.set (state,Status.init) >> M.create_state 5 >>
 Path.ttt2 ~p:true fresh t p4 (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "c" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 assert (Automaton.size a' = 14);

 M.return ()
;;

Format.printf "testing module Path         ... ";;
ignore (M.run (S.empty 10,Status.init) test);;
Format.printf "ok@\n";;

(* Tests: Module Initial *)
let test =
 M.create_state 1 >>= fun p1 -> M.create_state 2 >>= fun p2 ->
 M.create_state 3 >>= fun p3 -> M.create_state 4 >>= fun p4 ->
 M.create_state 5 >>= fun p5 -> M.create_state 6 >>= fun p6 ->
 M.create_state 7 >>= fun p7 -> M.create_state 8 >>= fun p8 ->
 M.create_state 9 >>= fun p9 -> M.create_state 10 >>= fun p10 ->
 M.create_state 11 >>= fun p11 -> M.create_state 12 >>= fun p12 ->
 M.create_state 13 >>= fun p13 -> M.create_state 14 >>= fun p14 ->
 M.create_state 15 >>= fun p15 ->
 let ps = ["1";"2";"3";"4";"5";"6";"7";"8";"9";"10";"11";"12";"13";"14";"15"] in
 let vs = ["x";"y";"z"] in
 Term.of_string vs ps "f(1,f(a,1))" >>= fun s ->
 Term.of_string vs ps "h(a,1,g(b))" >>= fun t ->
 Term.of_string vs ps "g(f(1,g(b)))" >>= fun u ->
 Term.of_string vs ps "g(b)" >>= fun v ->

 let size f a =
  Automaton.fold (fun l _ n ->
   if Option.fold ((=) f) false (Lhs.root l) then n+1 else n) a 0
 in

 (* functions individual, min, split *)
 M.create_fun 0 "a" >>= fun fa -> M.create_fun 0 "b" >>= fun fb ->
 M.create_fun 1 "g" >>= fun fg -> M.create_fun 2 "f" >>= fun ff ->
 M.create_fun 3 "h" >>= fun fh ->

 let fs = [ff;fg] and gs = [fa;fb;fh] in
 Initial.individual fs gs >>= fun a ->
 assert (size fa a = 1);
 assert (size fb a = 1);
 assert (size fg a = 3);
 assert (size ff a = 9);
 assert (size fh a = 27);
 assert (List.length (Automaton.finals a) = 3);
 assert (Automaton.size a = 41);

 let fs = [fg] and gs = [fa;fb;ff;fh] in
 Initial.individual fs gs >>= fun a ->
 assert (size fa a = 1);
 assert (size fb a = 1);
 assert (size fg a = 2);
 assert (size ff a = 4);
 assert (size fh a = 8);
 assert (List.length (Automaton.finals a) = 2);
 assert (Automaton.size a = 16);

 let fs = [fa;fb;fg;ff;fh] in
 Initial.min fs >>= fun a ->
 assert (size fa a = 1);
 assert (size fb a = 1);
 assert (size fg a = 1);
 assert (size ff a = 1);
 assert (size fh a = 1);
 assert (List.length (Automaton.finals a) = 1);
 assert (Automaton.size a = 5);

 let fs = [fa;fb;fg;ff;fh] in
 Initial.split fs >>= fun a ->
 assert (size fa a = 1);
 assert (size fb a = 1);
 assert (size fg a = 5);
 assert (size ff a = 25);
 assert (size fh a = 125);
 assert (List.length (Automaton.finals a) = 5);
 assert (Automaton.size a = 157);

 (* function specific *)
 let fresh_funs =
  let fresh t a = match t with
   | Lhs.Fun (f,[]) ->
    Automaton.find t a >>= Option.fold (M.return <.> Rhs.max) M.fresh_state
   | _ -> M.fresh_state
  in
  Path.fresh_reuse ~f:fresh
 in
 let fresh_state = const (M.liftM List.singleton M.fresh_state) in
 M.get >>= fun (state,_) -> M.set (state,Status.init) >> M.create_state 5 >>
 Initial.specific fresh_state fresh_funs [s;t;u;v] >>= fun a ->
 Lhs.of_string ps "a" >>= fun l -> Automaton.find l a >>= fun r ->
 assert (Rhs.mem p7 (Option.the r));
 Lhs.of_string ps "f(7,1)" >>= fun l -> Automaton.find l a >>= fun r ->
 assert (Rhs.mem p8 (Option.the r));
 Lhs.of_string ps "f(1,8)" >>= fun l -> Automaton.find l a >>= fun r ->
 assert (Rhs.mem p6 (Option.the r));
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l a >>= fun r ->
 assert (Rhs.mem p10 (Option.the r));
 Lhs.of_string ps "g(10)" >>= fun l -> Automaton.find l a >>= fun r ->
 assert (Rhs.mem p11 (Option.the r));
 Lhs.of_string ps "h(7,1,11)" >>= fun l -> Automaton.find l a >>= fun r ->
 assert (Rhs.mem p9 (Option.the r));
 Lhs.of_string ps "f(1,11)" >>= fun l -> Automaton.find l a >>= fun r ->
 assert (Rhs.mem p13 (Option.the r));
 Lhs.of_string ps "g(13)" >>= fun l -> Automaton.find l a >>= fun r ->
 assert (Rhs.mem p12 (Option.the r));
 assert (Automaton.size a = 8);
 assert (List.mem p6 (Automaton.finals a));
 assert (List.mem p9 (Automaton.finals a));
 assert (List.mem p11 (Automaton.finals a));
 assert (List.mem p12 (Automaton.finals a));
 assert (List.length (Automaton.finals a) = 4);

 (* function instances *)
 let s = 
  "a -> 1 \
   f(3,1) -> 2 \
   f(3,3) -> 2 \
   f(4,6) -> 5 \
   f(4,10) -> 11 \
   f(1,2) -> 2 \
   f(1,4) -> 6 \
   f(2,1) -> 2 \
   f(2,3) -> 2 \
   f(3,2) -> 2 \
   f(1,1) -> 2 \
   f(1,3) -> 2 \
   f(2,2) -> 2 \
   b -> 1 \
   g(2) -> 3 \
   g(11) -> 9 \
   g(1) -> 3 \
   g(1) -> 8 \
   g(1) -> 10 \
   g(3) -> 3 \
   h(1,4,8) -> 7 \
   1 -> 4 \
   2 -> 4 \
   3 -> 4"
 in
 Automaton.of_string ps s >>= fun a ->
 let a = Automaton.set_finals [p9;p7;p5] a in
 M.get >>= fun (state,_) -> M.set (state,Status.init) >> M.create_state 11 >>
 Term.of_string vs ps "f(x,f(a,x))" >>= fun s ->
 Term.of_string vs ps "h(a,x,g(b))" >>= fun t ->
 Term.of_string vs ps "g(f(x,g(b)))" >>= fun u ->
 let fs = [ff;fg] and gs = [fa;fb] in
 M.get >>= fun (state,_) -> M.set (state,Status.init) >> M.create_state 0 >>
 Initial.instances fresh_state fresh_funs fs gs [s;t;u] >>= fun b ->
 assert (a = b);

 let fs = [ff;fg] and gs = [fa;fb] in
 Initial.instances fresh_state fresh_funs fs gs [] >>= fun a ->
 assert (List.length (Automaton.finals a) = 0);
 assert (Automaton.size a = 0);

 (* function custom *)
 let fs = [fh] and gs = [ff;fg] and hs = [fa;fb] in
 M.get >>= fun (state,_) -> M.set (state,Status.init) >> M.create_state 1 >>
 Initial.custom fs gs hs >>= fun a ->
 assert (size fa a = 1);
 assert (size fb a = 1);
 assert (size fg a = 3);
 assert (size ff a = 9);
 assert (size fh a = 27);
 assert (List.length (Automaton.finals a) = 1);
 assert (Automaton.size a = 41);

 let fs = [] and gs = [ff;fg] and hs = [fa;fb] in
 M.get >>= fun (state,_) -> M.set (state,Status.init) >> M.create_state 1 >>
 Initial.custom fs gs hs >>= fun a ->
 assert (List.length (Automaton.finals a) = 0);
 assert (Automaton.size a = 0);

 (* function normal *)
 let fs = [fa;fg;ff;fh] in
 M.lift (T.of_string ["x";"y";"z"]
  "h(x,y,z) -> x
   f(x,a) -> x
   f(g(a),x) -> x") >>= fun trs ->
 Initial.normal fs trs >>= fun a ->
 assert (size fa a = 1);
 assert (size fg a = 3);
 assert (size ff a = 4);
 assert (size fh a = 0);
 assert (List.length (Automaton.finals a) = 1);
 assert (Automaton.size a = 11);

 let fs = [fa;fg;ff;fh] in
 M.lift (T.of_string ["x"]
  "h(x,x,x) -> x
   f(x,a) -> x
   f(g(a),x) -> x") >>= fun trs ->
 Initial.normal fs trs >>= fun a ->
 assert (size fa a = 1);
 assert (size fg a = 3);
 assert (size ff a = 4);
 assert (size fh a = 27);
 assert (List.length (Automaton.finals a) = 1);
 assert (Automaton.size a = 38);

 let fs = [fa;fg;ff] in
 Initial.normal fs Trs.empty >>= fun a ->
 assert (size fa a = 1);
 assert (size fg a = 1);
 assert (size ff a = 1);
 assert (List.length (Automaton.finals a) = 1);
 assert (Automaton.size a = 3);

 let fs = [fa;fg;ff] in
 M.lift (T.of_string ["x";"y"]
  "g(g(x)) -> x
   f(g(x),y) -> x
   f(f(a,g(x)),y) -> x") >>= fun trs ->
 Initial.normal fs trs >>= fun a ->
 assert (size fa a = 1);
 assert (size fg a = 3);
 assert (size ff a = 8);
 assert (List.length (Automaton.finals a) = 1);
 assert (Automaton.size a = 16);

 let fs = [fa;fg;ff] in
 M.lift (T.of_string ["x";"y";"z"]
  "g(g(x)) -> x
   f(g(y),z) -> y
   f(f(a,g(z)),x) -> z") >>= fun trs ->
 Initial.normal fs trs >>= fun a ->
 assert (size fa a = 1);
 assert (size fg a = 3);
 assert (size ff a = 8);
 assert (List.length (Automaton.finals a) = 1);
 assert (Automaton.size a = 16);

 let fs = [fa;fg;ff] in
 M.lift (T.of_string ["x";"y";"z"]
  "g(f(x,g(y))) -> x
   g(f(y,g(z))) -> x
   g(f(z,g(x))) -> x") >>= fun trs ->
 Initial.normal fs trs >>= fun a ->
 assert (size fa a = 1);
 assert (size fg a = 2);
 assert (size ff a = 9);
 assert (List.length (Automaton.finals a) = 1);
 assert (Automaton.size a = 15);

 let fs = [fa;fg;ff] in
 M.lift (T.of_string ["x";"y";"z"] "x -> y") >>= fun trs ->
 Initial.normal fs trs >>= fun a ->
 assert (size fa a = 0);
 assert (size fg a = 0);
 assert (size ff a = 0);
 assert (List.length (Automaton.finals a) = 0);
 assert (Automaton.size a = 0);
 M.return ()
;;

Format.printf "testing module Initial      ... ";;
ignore (M.run (S.empty 10,Status.init) test);;
Format.printf "ok@\n";;

(* Tests: Module Reachability *)
let test =
 M.create_fun 0 "a" >>= fun fa -> M.create_fun 0 "b" >>= fun fb ->
 M.create_fun 1 "g" >>= fun fg -> M.create_fun 2 "f" >>= fun ff ->
 M.create_fun 0 "c" >>= fun fc -> M.create_fun 3 "i" >>= fun fi ->
 M.create_fun 2 "h" >>= fun fh ->
 M.create_state 1 >>= fun p1 -> M.create_state 2 >>= fun p2 ->
 M.create_state 3 >>= fun p3 -> M.create_state 4 >>= fun p4 ->
 M.create_state 5 >>= fun p5 -> M.create_state 6 >>= fun p6 ->
 M.create_state 7 >>= fun p7 -> M.create_state 8 >>= fun p8 ->
 M.create_state 9 >>= fun p9 -> M.create_state 10 >>= fun p10 ->
 M.create_state 11 >>= fun p11 -> M.create_state 12 >>= fun p12 ->
 M.create_state 13 >>= fun p13 -> M.create_state 14 >>= fun p14 ->
 M.create_state 15 >>= fun p15 -> M.create_state 16 >>= fun p16 ->
 M.create_state 17 >>= fun p17 -> M.create_state 18 >>= fun p18 ->
 M.create_state 19 >>= fun p19 -> M.create_state 20 >>= fun p20 ->
 M.create_state 21 >>= fun p21 -> M.create_state 22 >>= fun p22 ->
 M.get >>= fun (state,_) -> M.set (state,Status.add_state p15 Status.init) >>
 let ps = ["1";"2";"3";"4";"5";"6";"7";"8";"9";"10"] in
 let ps = ps @ ["11";"12";"13";"14";"15";"16";"17";"18";"19"] in
 let s = 
  "a -> 1 \
   b -> 2 \
   f(1,2) -> 3"
 in
 Automaton.of_string ps s >>= fun a ->
 let a = Automaton.add_final p3 a in
 let s = "a -> 1" in
 Automaton.of_string ps s >>= fun b ->
 let b = Automaton.add_final p1 b in
 let s = 
  "a -> 1 \
   a -> 2 \
   b -> 1 \
   b -> 3 \
   c -> 1 \
   i(1,1,1) -> 1 \
   I(2,3,1) -> 4"
 in
 Automaton.of_string ps s >>= fun c ->
 let c = Automaton.add_final p4 c in
 let s = 
  "a -> 1 \
   b -> 2 \
   h(2,1) -> 3 \
   f(3,2) -> 4"
 in
 Automaton.of_string ps s >>= fun d ->
 let d = Automaton.add_final p4 d in

 (* function predecessors *)
 (*
 predecessors trs: f(a,b), f(a,a), g(a)

 automaton: a -> {1,2}
            b -> 2
            f({1,2},2) -> 3
            f({1,2},{1,2}) -> 3
            g({1,2}) -> 3

 predecessors trs: a, f(g(_),a), f(a,a), g(a), f(g(_),f(g(_),a)), ...
 
 inital automaton: a -> 1,3
                   b -> 3
                   f(3,3) -> 3
                   g(3) -> 2,3

 automaton: a -> {1,2,3}
            b -> 3
            f(2,1) -> 1
            f(2,2) -> 2
            f(2,3) -> 3
            f(2,{1,2}) -> {1,2}
            f(2,{1,3}) -> {1,3}
            f(2,{2,3}) -> {2,3}
            f(2,{1,2,3}) -> {1,2,3}
            f(3,{2,3}) -> 3
            f(3,3) -> 3
            f(3,{1,2,3}) -> 3
            f(3,{1,3}) -> 3
            f({1,2},1) -> 1
            f({1,2},2) -> 2
            f({1,2},3) -> 3
            f({1,2},{1,2}) -> {1,2}
            f({1,2},{1,3}) -> {1,3}
            f({1,2},{2,3}) -> {2,3}
            f({1,2},{1,2,3}) -> {1,2,3}
            f({1,3},3) -> 3
            f({1,3},{1,3}) -> 3
            f({1,3},{2,3}) -> 3
            f({1,3},{1,2,3}) -> 3
            f({2,3},1) -> 1
            f({2,3},2) -> 2
            f({2,3},3) -> 3
            f({2,3},{1,2}) -> {1,2}
            f({2,3},{1,3}) -> {1,3}
            f({2,3},{2,3}) -> {2,3}
            f({2,3},{1,2,3}) -> {1,2,3}
            f({1,2,3},1) -> 1
            f({1,2,3},2) -> 2
            f({1,2,3},3) -> 3
            f({1,2,3},{1,2}) -> {1,2}
            f({1,2,3},{1,3}) -> {1,3}
            f({1,2,3},{2,3}) -> {2,3}
            f({1,2,3},{1,2,3}) -> {1,2,3}
            g(2) -> 2
            g(3) -> {2,3}
            g({1,2}) -> {1,2}
            g({1,3}) -> {2,3}
            g({2,3}) -> {2,3}
            g({1,2,3}) -> {1,2,3}

 predecessors trs: f(h(b,a),b), f(a,b)
 
 inital automaton: a -> 1
                   b -> 2
                   h(2,1) -> 3
                   f(3,2) -> 4

 automaton: a -> {1,3}
            b -> 2
            h(2,{1,3}) -> 3
            f(3,2) -> 4
            f({1,3},2) -> 4
 *)
 let vs = ["x";"y";"z"] in
 let i =
  "a -> b \
   g(x) -> f(x,x)"
 in
 M.get >>= fun (s,status) ->
 let (trs,s) = Either.right (R.eval s (Trs.of_string vs i)) in
 M.set (s,status) >>
 Reachability.predecessors [fa;fb;fg;ff] trs (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "a" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p18 (Option.the r));
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p2 (Option.the r));
 Lhs.of_string ps "f(18,2)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p3 (Option.the r));
 Lhs.of_string ps "f(18,18)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p3 (Option.the r));
 Lhs.of_string ps "g(18)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p3 (Option.the r));
 assert (Automaton.finals a' = [p3]);
 assert (Automaton.size a' = 5);

 let i =
  "f(g(x),y) -> y \
   g(x) -> f(x,x) \
   a -> g(a)"
 in
 M.get >>= fun (s,status) ->
 let (trs,s) = Either.right (R.eval s (Trs.of_string vs i)) in
 M.set (s,Status.add_state p15 Status.init) >>= fun _ ->
 Reachability.predecessors [fa;fb;fg;ff] trs (Automaton.copy b) >>= fun b' ->
 Lhs.of_string ps "a" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p19 (Option.the r));
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p17 (Option.the r));
 Lhs.of_string ps "f(16,1)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 Lhs.of_string ps "f(16,16)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p16 (Option.the r));
 Lhs.of_string ps "f(16,17)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p17 (Option.the r));
 Lhs.of_string ps "f(16,18)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p18 (Option.the r));
 Lhs.of_string ps "f(16,19)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p19 (Option.the r));
 Lhs.of_string ps "f(16,20)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p20 (Option.the r));
 Lhs.of_string ps "f(16,21)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p21 (Option.the r));
 Lhs.of_string ps "f(17,17)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p17 (Option.the r));
 Lhs.of_string ps "f(17,18)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p17 (Option.the r));
 Lhs.of_string ps "f(17,19)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p17 (Option.the r));
 Lhs.of_string ps "f(17,21)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p17 (Option.the r));
 Lhs.of_string ps "f(18,1)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 Lhs.of_string ps "f(18,16)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p16 (Option.the r));
 Lhs.of_string ps "f(18,17)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p17 (Option.the r));
 Lhs.of_string ps "f(18,18)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p18 (Option.the r));
 Lhs.of_string ps "f(18,19)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p19 (Option.the r));
 Lhs.of_string ps "f(18,20)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p20 (Option.the r));
 Lhs.of_string ps "f(18,21)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p21 (Option.the r));
 Lhs.of_string ps "f(19,1)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 Lhs.of_string ps "f(19,16)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p16 (Option.the r));
 Lhs.of_string ps "f(19,17)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p17 (Option.the r));
 Lhs.of_string ps "f(19,18)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p18 (Option.the r));
 Lhs.of_string ps "f(19,19)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p19 (Option.the r));
 Lhs.of_string ps "f(19,20)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p20 (Option.the r));
 Lhs.of_string ps "f(19,21)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p21 (Option.the r));
 Lhs.of_string ps "f(20,1)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 Lhs.of_string ps "f(20,16)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p16 (Option.the r));
 Lhs.of_string ps "f(20,17)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p17 (Option.the r));
 Lhs.of_string ps "f(20,18)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p18 (Option.the r));
 Lhs.of_string ps "f(20,19)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p19 (Option.the r));
 Lhs.of_string ps "f(20,20)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p20 (Option.the r));
 Lhs.of_string ps "f(20,21)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p21 (Option.the r));
 Lhs.of_string ps "f(21,17)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p17 (Option.the r));
 Lhs.of_string ps "f(21,18)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p17 (Option.the r));
 Lhs.of_string ps "f(21,19)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p17 (Option.the r));
 Lhs.of_string ps "f(21,21)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p17 (Option.the r));
 Lhs.of_string ps "g(16)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p16 (Option.the r));
 Lhs.of_string ps "g(17)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p18 (Option.the r));
 Lhs.of_string ps "g(18)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p18 (Option.the r));
 Lhs.of_string ps "g(19)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p19 (Option.the r));
 Lhs.of_string ps "g(20)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p20 (Option.the r));
 Lhs.of_string ps "g(21)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p18 (Option.the r));
 assert (Automaton.finals b' = [p21;p1;p20;p19]);
 assert (Automaton.size b' = 44);

 let i = "x -> h(b,x)" in
 M.get >>= fun (s,status) ->
 let (trs,s) = Either.right (R.eval s (Trs.of_string vs i)) in
 M.set (s,Status.add_state p15 Status.init) >>= fun _ ->
 Reachability.predecessors [fa;fb;ff;fh] trs (Automaton.copy d) >>= fun d' ->
 Lhs.of_string ps "a" >>= fun l -> Automaton.find l d' >>= fun r ->
 assert (Rhs.mem p16 (Option.the r));
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l d' >>= fun r ->
 assert (Rhs.mem p2 (Option.the r));
 Lhs.of_string ps "h(2,16)" >>= fun l -> Automaton.find l d' >>= fun r ->
 assert (Rhs.mem p3 (Option.the r));
 Lhs.of_string ps "f(3,2)" >>= fun l -> Automaton.find l d' >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 Lhs.of_string ps "f(16,2)" >>= fun l -> Automaton.find l d' >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 assert (Automaton.finals d' = [p4]);
 assert (Automaton.size d' = 5);

 (* function successors *)
 (*
 successors trs: f(a,b),f(a,a),g(_)

 transducer: a -> 18                    a -> 16,19
             b -> 16,18                 b -> 19
             f(18,18) -> 17,18          f(19,19) -> 19
             g(18) -> 18                g(19) -> 17,19
             16 -> 18                   16 -> 19
             17 -> 18                   17 -> 19

 automaton: a -> 1,16,19
            b -> 2,19
            f(1,2) -> 3
            f(19,19) -> 19
            g(19) -> 17,19
            16 -> 2,19
            17 -> 3,19


 successors trs: a, f(a,_), f(g(_),_), f(f(g(_),_),_), g(_), ...

 transducer: a -> 19,20                 a -> 18,21
             b -> 19                    b -> 21
             f(19,19) -> 17,19          f(21,21) -> 21
             g(19) -> 19                f(22,21) -> 16
             g(20) -> 18                g(21) -> 17,21,22
             16 -> 17,18,19,20          16 -> 17,18,21,22
             17 -> 16,18,19,20          17 -> 16,18,21,22
             18 -> 16,17,19,20          18 -> 16,17,21,22
             19 -> 16

 automaton: a -> 1,18,21
            b -> 21
            f(21,21) -> 21
            f(22,21) -> 16
            g(21) -> 17,21,22
            16 -> 1,17,18,21,22
            17 -> 1,16,18,21,22
            18 -> 1,16,17,21,22
 *)
 let vs = ["p";"v";"w";"x";"y";"z"] in
 let i =
  "b -> a \
   f(x,y) -> g(z)"
 in
 M.get >>= fun (s,status) ->
 let (trs,s) = Either.right (R.eval s (Trs.of_string vs i)) in
 M.set (s,Status.add_state p15 Status.init) >>
 Reachability.successors [fa;fb;fg;ff] trs (Automaton.copy a) >>= fun a' ->
 Lhs.of_string ps "a" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p16 (Option.the r));
 assert (Rhs.mem p19 (Option.the r));
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p2 (Option.the r));
 assert (Rhs.mem p19 (Option.the r));
 Lhs.of_string ps "f(1,2)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p3 (Option.the r));
 Lhs.of_string ps "f(19,19)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p19 (Option.the r));
 Lhs.of_string ps "g(19)" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p17 (Option.the r));
 assert (Rhs.mem p19 (Option.the r));
 Lhs.of_string ps "16" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p2 (Option.the r));
 assert (Rhs.mem p19 (Option.the r));
 Lhs.of_string ps "17" >>= fun l -> Automaton.find l a' >>= fun r ->
 assert (Rhs.mem p3 (Option.the r));
 assert (Rhs.mem p19 (Option.the r));
 assert (Automaton.finals a' = [p3]);
 assert (Automaton.size a' = 13);

 let i =
  "x -> f(g(y),z) \
   f(x,y) -> g(z) \
   g(a) -> a"
 in
 M.get >>= fun (s,status) ->
 let (trs,s) = Either.right (R.eval s (Trs.of_string vs i)) in
 M.set (s,Status.add_state p15 Status.init) >>
 Reachability.successors [fa;fb;fg;ff] trs (Automaton.copy b) >>= fun b' ->
 Lhs.of_string ps "a" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p18 (Option.the r));
 assert (Rhs.mem p21 (Option.the r));
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p21 (Option.the r));
 Lhs.of_string ps "f(21,21)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p21 (Option.the r));
 Lhs.of_string ps "f(22,21)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p16 (Option.the r));
 Lhs.of_string ps "g(21)" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p17 (Option.the r));
 assert (Rhs.mem p21 (Option.the r));
 assert (Rhs.mem p22 (Option.the r));
 Lhs.of_string ps "16" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p17 (Option.the r));
 assert (Rhs.mem p18 (Option.the r));
 assert (Rhs.mem p21 (Option.the r));
 assert (Rhs.mem p22 (Option.the r));
 Lhs.of_string ps "17" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p16 (Option.the r));
 assert (Rhs.mem p18 (Option.the r));
 assert (Rhs.mem p21 (Option.the r));
 assert (Rhs.mem p22 (Option.the r));
 Lhs.of_string ps "18" >>= fun l -> Automaton.find l b' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p16 (Option.the r));
 assert (Rhs.mem p17 (Option.the r));
 assert (Rhs.mem p21 (Option.the r));
 assert (Rhs.mem p22 (Option.the r));
 assert (Automaton.finals b' = [p1]);
 assert (Automaton.size b' = 24);

 let i =
  "i(x,y,z) -> i(a,b,w) \
   a -> c \
   b -> c"
 in
 M.get >>= fun (s,status) ->
 let (trs,s) = Either.right (R.eval s (Trs.of_string vs i)) in
 M.set (s,Status.add_state p15 Status.init) >>
 Reachability.successors [fa;fb;fc;fi] trs (Automaton.copy c) >>= fun c' ->
 Lhs.of_string ps "a" >>= fun l -> Automaton.find l c' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p2 (Option.the r));
 assert (Rhs.mem p20 (Option.the r));
 assert (Rhs.mem p22 (Option.the r));
 Lhs.of_string ps "b" >>= fun l -> Automaton.find l c' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p3 (Option.the r));
 assert (Rhs.mem p20 (Option.the r));
 assert (Rhs.mem p21 (Option.the r));
 Lhs.of_string ps "c" >>= fun l -> Automaton.find l c' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p17 (Option.the r));
 assert (Rhs.mem p18 (Option.the r));
 assert (Rhs.mem p20 (Option.the r));
 Lhs.of_string ps "i(1,1,1)" >>= fun l -> Automaton.find l c' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 Lhs.of_string ps "i(20,20,20)" >>= fun l -> Automaton.find l c' >>= fun r ->
 assert (Rhs.mem p20 (Option.the r));
 Lhs.of_string ps "i(22,21,20)" >>= fun l -> Automaton.find l c' >>= fun r ->
 assert (Rhs.mem p16 (Option.the r));
 Lhs.of_string ps "I(2,3,1)" >>= fun l -> Automaton.find l c' >>= fun r ->
 assert (Rhs.mem p4 (Option.the r));
 Lhs.of_string ps "16" >>= fun l -> Automaton.find l c' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p20 (Option.the r));
 Lhs.of_string ps "17" >>= fun l -> Automaton.find l c' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p2 (Option.the r));
 assert (Rhs.mem p20 (Option.the r));
 assert (Rhs.mem p22 (Option.the r));
 Lhs.of_string ps "18" >>= fun l -> Automaton.find l c' >>= fun r ->
 assert (Rhs.mem p1 (Option.the r));
 assert (Rhs.mem p3 (Option.the r));
 assert (Rhs.mem p20 (Option.the r));
 assert (Rhs.mem p21 (Option.the r));
 assert (Automaton.finals c' = [p4]);
 assert (Automaton.size c' = 26);
 M.return ()
;;

Format.printf "testing module Reachability ... ";;
ignore (M.run (S.empty 10,Status.init) test);;
Format.printf "ok@\n";;
