open Util;;
open Logic;; (* use <?> operator from Logic and not from Util *)
module Number = Logic.Number;;
open Operators;;


type t = Gt of int * int | Eq of int * int;;

let arith = 
 {Logic.min = Int64.of_int 100; 
 neg = true; 
 rat = 1; 
 real = false; 
 minf = false};;

let test sop op a b c = 
 if not ((op a b) = c) then Format.printf "%a %s %a <> %a@\n"
  Number.fprintf a sop Number.fprintf b Number.fprintf c
;;

let check sop a b c = match sop with
 | "+" -> test sop Number.add a b c
 | "-" -> test sop Number.sub a b c
 | "*" -> test sop Number.mul a b c
;;

let check_cp cop a b c = match cop with
 | ">" -> assert (Number.gt a b = c)
 | "=" -> assert (Number.eq a b = c)
;;

let check_eq va a =
 Format.fprintf Format.str_formatter "%a" Number.fprintf va; 
 let x = Format.flush_str_formatter () in
 Format.fprintf Format.str_formatter "%a" Logic.fprintf_a a; 
 let y = Format.flush_str_formatter () in
 assert (x = y);
;;

let test_op s op sop a b = 
 let result = 
 fresh_arith arith >>= fun x ->
 fresh_arith arith >>= fun y ->
 fresh_arith arith >>= fun z ->
 let c = op x y in
 solve ~solver:s ((a <=> x) <&> (b <=> y) <&> (c <=> z)) >>= function 
  | None -> (return "no")
  | Some assign -> (
   eval_a x assign >>= fun va ->
   eval_a y assign >>= fun vb ->
   eval_a z assign >>= fun vz ->
   check sop va vb vz;
   check_eq va a;
   check_eq vb b;
   check sop va vb vz;
   return "yes")
 in
 (*ignore (run result); *)
 match run ~obits:max_int result with
  | "no"  ->
   Format.printf "%s: number %a or %a cannot be represented@\n@?" sop
   Logic.fprintf_a a Logic.fprintf_a b;
   ();
  | "yes" -> 
   ();
;;

let test_cop s op cop a b = 
 let c = op (fresh a) (fresh b) in
 let result = 
 solve ~solver:s c >>= function 
  | None -> return "no";
  | Some assign -> (
   eval_a (fresh a) assign >>= fun va ->
   eval_a (fresh b) assign >>= fun vb ->
   eval_p c assign >>= fun vc ->
   check_cp cop va vb vc;
   return "yes")
 in
 let x = run ~obits:max_int result in
 ()
;;

let test_ops s a b = 
 test_op s (<+>) "+" a b;
 test_op s (<->) "-" a b;
 test_op s (<*>) "*" a b;
 test_cop s (<>>) ">" a b;
 test_cop s (<=>) "=" a b;
;;

let test_from_to s a b d = 
 let ns = (List.range a b) in
 let ds = List.range 1 (d + 1) in
 let ns = List.product ns ds in
 let ns = List.map (fun (n,d) -> 
  (Big_int.big_int_of_int n, Big_int.big_int_of_int d)) ns in
 let ns = List.map (fun (n,d) -> Number.of_big_rat n d) ns in
 let ns = List.map constant ns in
 let ss = List.square ns in
 List.iter (fun (a,b) -> test_ops s a b) ss
;;

(*
let cache f tbl k = 
 (if not (Hashtbl.mem tbl k) then
  f >>= fun x -> Hashtbl.add tbl k x; return tbl
 else
  return tbl) >>= fun tbl ->
 return (Hashtbl.find tbl k)
;;

let cache_bool = cache fresh_bool;;
let a_spec = {min=Int.pow 2 10;rat=1;real=1;neg=false;minf=false};;
let b_spec = {min=7;rat=1;real=1;neg=true;minf=false};;
let cache_arith ?(spec = a_spec) tbl = cache (fresh_arith spec) tbl;;
*)

(*
let test n =
 let a = constant (Number.of_int n) in
 let result = 
  fresh_arith arith >>= fun x ->
   solve ~solver:MiniSat ((x <=> a))  >>= function
   | None -> return "shit"
   | Some assign -> 
     (*Format.printf "Assign %a\n" Logic.fprintf_assignment assign; *)
     (*Format.printf "a = %a\n" Logic.fprintf_a a; *)
     (*Format.printf "x = %a\n" Logic.fprintf_a x; *)
     eval_a x assign >>= fun va ->
     Format.printf "%d = %a@\n" n Number.fprintf va;
     return "yes"
  in
  Format.printf "Surprise: %s\n" (Logic.run result);
  (*ignore (Logic.run result); *)
;;
*)

let test () = 
 test_from_to MiniSat ~-8 9 1;
 Format.printf "all tests done@\n";
;;


(*
let test () =
 let ppf = Format.std_formatter in
 Format.fprintf ppf "Testing module Logic ...\n";
 (*test_from_to MiniSat ~-5 10 2; *)
 (*test_from_to Yices ~-5 5 1; *)

 (*List.iter test (List.range ~-20 20); *)
(*
*)
 let x0 = constant (Number.of_int ~-1) in
 let x1 = constant (Number.of_int 0) in
 let result = 
 fresh_arith (Logic.int 1000) >>= fun a ->
 (*fresh_arith (Logic.nat 1) >>= fun b ->  *)
 Format.printf "%a max %a=@\n" Logic.fprintf_a x0 Logic.fprintf_a x1;
 let c = a <=> (max x0 x1) in
 solve ~solver:MiniSat (c) >>= function
  | None -> (return "no")
  | Some assign -> (
    eval_a a assign >>= fun vc -> 
     Format.printf "%a = %a\n" fprintf_a a Number.fprintf vc;
   return "yes") ;
 in
 let x = run ~obits:8 result in
 Format.printf "%s\n" x;
 ();
 exit 0;
  
(*
 let btbl = Hashtbl.create 512 in
 let atbl = Hashtbl.create 512 in
 let result = 
 cache_bool btbl 0 >>= fun x ->
 cache_bool btbl 1 >>= fun y ->
 cache_arith atbl 0 >>= fun a ->
 cache_arith atbl 1 >>= fun b ->
 cache_arith atbl 2 >>= fun c ->
 cache_arith atbl 3 >>= fun d ->
 let pow3 x = x <*> x <*> x in
 let f = 
  ((pow3 a <+> pow3 d) <=> (pow3 b <+> pow3 c))
  <&> (zero <<> a) <&> (a <<> b) <&> (b <<> c) <&> (c <<> d) in
 Format.printf "formula: %a\n%!" fprintf_p f;
 solve ~solver:MiniSat f >>= function
  | None -> (return "no")
  | Some assign -> (
    (* eval_p x assign >>= fun z -> *)
     (* Format.printf "%a = %b\n" fprintf_p x z; *)
    (* eval_p y assign >>= fun z -> *)
     (* Format.printf "%a = %b\n" fprintf_p y z; *)
    eval_a a assign >>= fun va -> 
     Format.printf "%a = %a\n" fprintf_a a Number.fprintf va;
   eval_a b assign >>= fun vb -> 
    Format.printf "%a = %a\n" fprintf_a b Number.fprintf vb;
   eval_a c assign >>= fun vc -> 
    Format.printf "%a = %a\n" fprintf_a c Number.fprintf vc;
   eval_a d assign >>= fun vd -> 
    Format.printf "%a = %a\n" fprintf_a d Number.fprintf vd;
   let pow3 x = Number.mul (Number.mul x x) x in
    Format.printf "%a = %a@\n" 
     Number.fprintf (Number.add (pow3 va) (pow3 vd))
     Number.fprintf (Number.add (pow3 vb) (pow3 vc));
   return "yes")
 in
 let x = run ~obits:11 result in
 Format.printf "%s\n" x;
 ()
 *)
;;
*)

(*
module N = struct
 include Number;;
 let combine = max;;
 let copy = id;;
 let compare = Pervasives.compare
end
module Ngraph = Graph.Labeled (N) (Int)
let test () =
 let l n = Some (Number.of_int n) in
 let g = Ngraph.generate (fun i j -> [(i,l (i+j),j)]) (List.range 0 26) in
 Format.printf "@[<1>G:@\n%a@]@\n%!" Ngraph.fprintf g;
 let rec foo g = 
  if List.length (Ngraph.nodes g) = 1 then () else
  let n = List.hd (Ngraph.nodes g) in
  let g = Ngraph.bypass n g in
  (*Format.printf "@[<1>G:@\n%a@]@\n%!" Ngraph.fprintf g; *)
  Format.printf "%d nodes, %d edges@\n%!" 
   (List.length (Ngraph.nodes g)) (List.length (Ngraph.edges g));
  (*foo g *)
 in
 foo g
;;
*)

(*
let test () = 
 let arith = Logic.int 10 in
 let result = 
 fresh_arith arith >>= fun x ->
 fresh_arith arith >>= fun y ->
 let c = (<*>) x y in
 let phi = (c <=> x) in
 let _ = Format.printf "%a\n" (Logic.fprintf_smt ~logic:("QF_NIA")) phi in
 return ()
 in
 ignore (run result); 
 ();
;;
*)

(*tmp begin*)
(*
(*** SUBMODULES **********************************************************)
module List = Util.List;;
module Var = Rewriting.Variable;;
module Sig = Rewriting.Signature;;
module L = Logic;;
module Op = L.Operators;;
module N = L.Number;;
module M = L.Monad;;

(*** OPENS (2) ***********************************************************)
open M;;

(*** TYPES ***************************************************************)
type linpoly = (int * Var.t) list
type t = linpoly * linpoly

let var_cache = Hashtbl.create 100

let (<.>) = Util.(<.>);;
let (<&>) = Op.(<&>);;
let (<=>) = Op.(<=>);;
let (<<=>) = Op.(<<=>);;
let big_and l = L.big_and l;;
let big_sum l = L.big_sum l;;
let var s v = L.cache_arith var_cache s v;;

(* equation constraint, s is spec defining natural number range *)
let polynomials s (xs,ys) =
 let poly zs = 
  let mono c v = var s v >>= fun x -> return (L.scale (N.of_int c) x) in
  let gs = List.group ~c:Var.compare zs in
  map (fun g -> mono (List.length g) (List.hd g)) gs >>=
  (return <.> big_sum)
 in
 project poly (xs,ys)
;;



(* return formula negating assignment *)
let negate = L.negate_assignment

(* call solver *)
let solve f = L.solve ~solver:L.Yices f

(* When computing a basis, an upper bound for all solution values is 
   given by the maximum of the abolute value of coefficients *)
let upper_bound (xs,ys) =
 let length zs = List.map List.length (List.group ~c:Var.compare zs) in
 let maxc zs = List.foldl max 0 (length zs) in
 max (maxc xs) (maxc ys)
;;

let smaller_than_upper_bound s b xs =
 let b = L.constant (N.of_int b) in
 map (fun x -> var s x >>= fun x -> return (x <<=> b)) xs >>= 
 (return <.> big_and)
;;

let to_ass s vars a = 
 let to_int v n = return (v,N.to_int n) in
 let val_of a v = var s v >>= Util.flip L.eval_a a >>= to_int v in
 M.map (val_of a) vars
;;

let all_solutions (xs,ys) = 
 let b = upper_bound (xs,ys) in
 let spec = L.nat b in
 let vars = List.unique (xs@ys) in
 polynomials spec (xs,ys) >>= fun (px,py) ->
 smaller_than_upper_bound spec b vars >>= fun f ->
 let rec all_solutions' f ass =
  (* L.fprintf_p Format.std_formatter f; Format.printf "\n%!"; *)
  match L.run (solve f >>= function
   | None -> return None
   | Some a -> 
   (* Format.printf "ass: %a@\n" L.fprintf_assignment a; *)
    let phi = negate a <&> f in
    to_ass spec vars a >>= fun ax ->
    return (Some (phi,ax)))
  with
   | None -> ass
   | Some (phi,ax) -> all_solutions' phi (ax::ass)
 in
 return (all_solutions' (f <&> (px <=> py)) [])
;;

(* Given  lists xs=[x1,x2,...,xn] and ys=[y1,y2,..,ym] find 
 all assignments such that x1+...+xn=y1+...+ym *)
let solve (xs,ys) = Logic.run (all_solutions (xs,ys))

let test () =
 let sigma = Sig.empty 20 in
 let x,sigma = Sig.create_var "x" sigma in
 let y,sigma = Sig.create_var "y" sigma in
 let z,sigma = Sig.create_var "z" sigma in
 let u,sigma = Sig.create_var "u" sigma in
 let v,sigma = Sig.create_var "v" sigma in
 let w,sigma = Sig.create_var "w" sigma in
 let var_name x = Sig.find_var_name x sigma in
 let var_names = List.foldl (fun s p -> (var_name p)^" "^s) "" in
 let value (x,n) = (var_name x)^":"^(string_of_int n)^" " in
 let print_ass a = List.foldl (fun s p -> (value p)^s) "" a in
 let print = List.foldl (fun s p -> (print_ass p)^", "^s) "" in
 let check (xs,ys) =
  Format.printf "Solving %s=%s yields\n %s\n%!" 
  (var_names xs) (var_names ys) (print (solve (xs,ys)))
 in
 check ([x; z], [y])
;;
*)
(*tmp end*)


test ();;





