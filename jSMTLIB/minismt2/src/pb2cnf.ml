(* $Id: pb2cnf.ml,v 1.14 2013/12/12 10:08:22 hzankl Exp $ *)

(* Copyright 2013 Sarah Winkler
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

(*** MODULES ******************************************************************)
module S = SmtFormula;;
module P = Parsec.StringParser;;
module H = Hashtbl;;

module F = struct
 include Format
 let formatter_of_out_channel c =
  let f = formatter_of_out_channel c in
  pp_set_margin f 9999;
  f
end

(*** OPENS (1) ****************************************************************)
open Util;;
open SmtFormula;;

(*** FUNCTIONS ****************************************************************)
let tmp_pb () = Filename.temp_file "minismt" ".pb";;
let tmp_cnf () = Filename.temp_file "minismt" ".cnf";;

let c2s = Int64.to_string;;

let fprintf_a ppf = 
 let rec p ppf = function
  | Vara v -> F.fprintf ppf "1 %a " va2f v
  | Const c -> F.fprintf ppf "%s " (c2s c)
  | Mul [Const c; Vara v]
  | Mul [Vara v; Const c] -> F.fprintf ppf "%s %a " (c2s c) va2f v
  | Add al ->  List.fprintf p "@ " ppf al
  | _ -> failwith "Undesired pattern in Pb2cnf.fprintf_a"
 in p ppf
;;


let fprintf = 
 let p ppf = function
  | Ge (a, Const c) -> F.fprintf ppf "%a >= %s ;" fprintf_a a (c2s c)
  | _ -> failwith "Undesired pattern in Pb2cnf.print"
 in List.fprintf p "@\n"
;;

let print f cs =
 let ch = open_out f in
 let ppf = F.formatter_of_out_channel ch in
 F.fprintf ppf "%a\n%!" fprintf cs;
 close_out ch
;;

let execvp cmd param =
 match Unix.fork () with
 | 0 -> Unix.execvp cmd param;
 | -1 ->
   let _ = Printf.eprintf "error occured on fork of %s\n%!" cmd in
   None
 | _ ->
   let _, state = Unix.wait () in
   match state with
   | Unix.WEXITED exitcode -> Some exitcode
   | _ -> None
;;

let number =
 let (>>=) = P.(>>=) in
 let (>>) = P.(>>) in
 P.oneof "123456789" >>= fun c -> P.many P.digit >>= fun cs -> P.spaces >>
 P.return (int_of_string (String.of_char_list (c::cs)))
;;

let var_map =
 let (>>=) = P.(>>=) in
 let (>>) = P.(>>) in
 let binding =
  number >>= fun k -> P.char ':' >> 
  P.char 'x' >> number >>= fun v -> P.spaces >> P.return (k,v)
 in
 P.char 'c' >> P.char 'v' >> P.spaces >> P.many binding >>= fun d ->
 P.return (Some (List.foldl (fun h (k,v) -> H.add h k v; h) (H.create 512) d))
;;

let pseudo_dimacs =
 let (>>=) = P.(>>=) in
 let (>>) = P.(>>) in
 let comment = P.char 'c' >> P.many (P.noneof "\n") >> P.spaces in
 let problem = P.char 'p' >> P.many (P.noneof "\n") >> P.spaces in
 let var =
  P.option true (P.char '-' >> P.return false) >>= fun b ->
  number >>= fun x -> P.spaces >> P.return (x, b)
 in
 let clause = P.many var >>= fun xs -> P.char '0' >> P.spaces >> P.return xs in
 P.spaces >>
 P.many problem >>
 P.many comment >>
 P.many clause >>= fun cs ->
 P.option None var_map >>= fun d ->
 P.eoi >>
 P.return (cs,d)
;;

let replace d c =
 let rep (x,b) = 
  (* replace variable if not newly introduced *)
  let x' = try H.find d x with Not_found -> x in ("x"^(string_of_int x'),b) 
 in 
 List.map (fun p -> try rep p with Not_found -> failwith "incomplete map") c

let str = List.map (fun (x,b) -> "x"^(string_of_int x),b)

let read f =
 let ts = Parsec.StringInput.of_file f in
 match P.parse pseudo_dimacs ts with
    Left e -> (Printf.eprintf "%s\n" (Parsec.Error.to_string e); exit 1)
  | Right (cs,d) -> 
   (match d with None -> List.map str cs 
               | Some d ->  List.map (replace d) cs)
;;


let run pbsolver fpb =
 let fcnf = tmp_cnf () in
 let cmds = (String.split pbsolver)@[fpb; "-cnf="^fcnf;] in
  let _ = Debug.debug ("exec cmd: " ^ (String.concat " " cmds)) in
 let exec _ =   execvp (List.hd cmds) (Array.of_list cmds) in
  let _ = Debug.debug "solver executed" in
 let res = match exec () with
  | Some i  -> if i = 0 then Some (read fcnf) else None
  | None -> None
 in
  let _ = Debug.debug "result read" in
 if not !Debug.on then (Sys.remove fpb; Sys.remove fcnf;);
 res
;;

let translate cs pbsolver =
 let f = tmp_pb () in
 print f cs;
 run pbsolver f
;;

