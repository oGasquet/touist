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
open Util;;
open Processors;;
open Rewritingx;;
open Parser.Xml;;

type flags = {
  parse_xml : bool ref;  
  parse_xml' : bool ref;
  trs : bool ref;
  file : string ref;
  trans : bool ref;
};;

let flags = {
  parse_xml = ref false;
  parse_xml' = ref false;
  trs = ref false;
  file = ref "";
  trans = ref false;
};;

let usage = "Usage: ./measure [options] <file>\n\n";;

let spec = Arg.alignx 80 [
  ("-px", Arg.Set flags.parse_xml, "run XML parser");
  ("-apx", Arg.Set flags.parse_xml', "run alternative XML parser");
  ("-trs", Arg.Set flags.trs, "run TRS parser");
  ("-trans", Arg.Set flags.trans, "internal XML transformation");
];;

let time txt f x =
  Printf.printf "%s ... %!" txt;
  let t = Unix.time () in
  let y = f x in
  let d = Unix.time () -. t in
  Printf.printf "took %.2f second(s)\n%!" d;
  y
;;

let main () =
 let file = ref true in
 let push s =
   if !file then (file := false; flags.file := s)
   else (Arg.usagex Format.err_formatter spec usage; exit 0)
 in
 Arg.parse spec push usage;
 let apx = time "parsing XML (alternative parser)" (fun chin ->
   snd (XmlParser.doc XmlLexer.token (Lexing.from_channel chin)))
 in
 let px = time "parsing XML" (fun chin ->
   let module XP = Parsec.Xml.MakeParser (Parsec.StringParser) in
   match XP.parse (Parsec.StringInput.of_channel chin) with
     | Left e      -> Pervasives.failwith (Parsec.Error.to_string e)
     | Right (_,x) -> x)
 in
 let trans p chin =
   let x = p chin in
   let m =
     XmlInput.problem   >>= fun p ->
     get_state          >>=
     (return <.> Pair.make p)
   in
   time "internal XML transformation" (fun x ->
     match run m (Signature.empty 100) x with
       | Left e -> Pervasives.failwith e
       | Right x -> x) x
 in
 let wst_trs = time "parsing WST TRS" (fun chin ->
   WstParser.Trs.of_channel chin)
 in
 Printf.printf "opening file '%s'\n%!" !(flags.file);
 let chin = open_in !(flags.file) in
 if !(flags.trs) then (
   let _ = wst_trs chin in exit 0
 ) else if !(flags.trans) then (
    (* measuere internal XML transformation *)
    let p = if !(flags.parse_xml') then apx else px in
    let _ = trans p chin in exit 0
  ) else if !(flags.parse_xml) then (
   (* measure XML parsing *)
   let _ = px chin in exit 0
 ) else if !(flags.parse_xml') then (
   (* measure alternative XML parsing *)
   let _ = apx chin in exit 0
 ) else (
   (* measure startup time *)
   exit 0
 )
;;
