module H = Hashtbl;;
open Util;;

(*
module String = struct
 type t = string;;
 let compare = compare;;
 let hash = Hashtbl.hash;;
 let copy = id;;
 let fprintf = String.fprintf;;
end

module Int = struct
 type t = int;;
 let compare = compare;;
 let hash = Hashtbl.hash;;
 let zero = 0;;
 let next = succ;;
 let fprintf = flip Format.fprintf "%d" ;;
 let copy = id;;
end

module Index = Isomorphism.Make (Int) (String);;
module Graph = Graph.Make (Int);;

let test () =
 let g = Graph.make [(1,1)] in
 let _ = match Graph.cycles 1 g with
  | [[1;1]] -> Format.printf "hooray@\n"
 in
 ()
;;

test();;
*)
(*
let test2 () =
 let m0 x = x + 1 in
 let m1 x = x + 10 in
 let m2 x = x + 10 in
 let x = ref false in
 let ls = [
  ("arctic",m0,"arctic interpretations (KW08)");
  ("bounds",m0,"matchbounds (KM09)");
  ("matrix",m1,"matrix interpretations (EWZ08)");
  ("uncurrying",m2,"uncurrying applicative systems (HMZ08)");
 ] in
 let args = List.map (fun (a,_,c) -> (a,Arg.Set x,c)) ls in
 let arga = Arg.alignx 80 args in
 Arg.usage arga "The following processors are available in TTT2";
;;

test2 ();;
*)

(*
let test3 () =
 let xs = List.range 0 100000 in
 let ys = List.rev_append xs (List.rev_append xs xs) in
 let unique ?(c = compare) xs =
  let t = H.create (List.length xs) in
  let add xs x = if H.mem t x then xs else (H.add t x 1; x::xs) in
  List.rev (List.foldl add [] xs)
 in
 Format.printf "@\ndata generated@\n%!";
 let ys = List.unique ys in
 Format.printf "length: %n@\n%!" (List.length ys)
;;

test3 ();;
*)

let test () =
 let rec loop x = Unix.sleep 1; loop x in
 let t1 = Process.Local 1.0 in
 let t2 = Process.Local 2.0 in
 let t3 = Process.Local 3.0 in
 let t4 = Process.Local 4.0 in
 let f i n x = ignore (Process.run_timed n loop x); i in
 let g i n x = ignore (Process.run_timed n loop x); loop x in
 let sleep n = fun _ -> Unix.sleep n in
 (*
 let _ = 
 Process.run_timed t1 
  (fun _ -> Process.run_parallel [
   fun _ -> Process.run_timed t1 (sleep 2) ();
   sleep 3] 1) () 
 in
 *)
 Process.run_timed t1 
  (fun x -> Process.run_timed t2 Unix.sleep 3; Unix.sleep 3) ();
 (* Process.run_timed t2 (Process.run_timed t3 loop; loop) (); *)
 ()
;;


test ();;


