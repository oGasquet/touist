(* $Id: bvlexer.mll,v 1.1 2010/01/01 14:08:30 hzankl Exp $ *)

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
{
(*** OPENS ********************************************************************)
 open Bvparser;;
}

let id = [^' ''\t''\n''\r''('')''"'',''~''{''}']+
let num = ['0'-'9']+

(* translate into tokens *)
rule token = parse
 | [' ' '\t' '\n'] {token lexbuf}
 | '('      { LPAREN }
 | ')'      { RPAREN }
 | '='      { EQ }
 | "true"   { TRUE }
 | "false"  { FALSE }
 | "sat"    { SAT }
 | "unsat"  { UNSAT }
 | "unknown"{ UNKNOWN }
 | id  as s { ID s }
 | eof {EOF}
