(* $Id: debug.ml,v 1.9 2013/10/21 08:35:44 hzankl Exp $ *)

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

let on = ref false;;
let t0 = Unix.gettimeofday ();;

let ltime () = 
 (* Format.fprintf Format.str_formatter "%g" ((Unix.gettimeofday ()) -. t0); *)
 Format.fprintf Format.str_formatter "%g" (Sys.time ());
 Format.flush_str_formatter ();
;;

let debug s = if !on then Format.eprintf "... %s (%s)@\n%!" s (ltime ());;
let debug2 () = if !on then Format.eprintf "... %s (%s)@\n%!" (Format.flush_str_formatter ()) (ltime ());;
let dprintf s = if !on then Format.eprintf "... %t (%s)@\n%!" s (ltime ());;

