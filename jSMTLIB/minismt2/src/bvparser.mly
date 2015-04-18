/* $Id: bvparser.mly,v 1.2 2010/01/01 16:03:01 hzankl Exp $

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
*/

/***HEADER***/ 
%{
 open Util;;
 let c2i = function '0' -> 0 | '1' -> 1;;
 let nat_of_bv s =
  let cs = List.map c2i (String.to_char_list s) in
  List.foldl1 (fun acc elt -> elt + 2*acc) cs
 ;;
 let int_of_bv n = 
  let sign = n.[2] and bits = String.sub n 3 (String.length n - 3) in
  let natval = nat_of_bv bits in
  let intval = if sign = '1' then natval - (Int.pow 2 (String.length bits)) else natval in
  Logic.Number.of_int intval
 ;;
%}

/***DECLARATIONS***/ 
%token <string> ID
%token LPAREN RPAREN 
%token EQ
%token SAT UNSAT UNKNOWN
%token TRUE FALSE
%token EOF
%start parse
%type <((string * Logic.Number.t) list * (string * bool) list) option> parse

/***RULES***/
%%
parse:
 all EOF {$1}
;

all: 
 | SAT      model {Some $2}
 | UNSAT    {None}
 | UNKNOWN  {None}


model:
 | {([],[])}
 | LPAREN EQ ID bv RPAREN model     {let (b,n) = $6 in (($3,$4)::b,n)}
 | LPAREN EQ ID bool RPAREN model   {let (b,n) = $6 in (b,($3,$4)::n)}

bool:
 | TRUE  {true}
 | FALSE {false}

bv:
 | ID {int_of_bv $1}
/***TRAILER***/ 
%%
