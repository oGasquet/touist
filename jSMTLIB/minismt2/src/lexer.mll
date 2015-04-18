(* $Id: lexer.mll,v 1.6 2010/01/08 14:12:43 hzankl Exp $ *)

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
 open Parser;;
}

let id = [^' ''\t''\n''\r''('')''"'',''~''{''}']+
let comment = '{' [^'}']+ '}'
let num = ['0'-'9']+

(* translate into tokens *)
rule token = parse
 | [' ' '\t' '\n' '\r'] {token lexbuf}
 | '+'      { ADD }
 | '-'      { SUB }
 | '*'      { MUL }
 | '('      { LPAREN }
 | ')'      { RPAREN }
 | "true"   { TOP }
 | "false"  { BOT }
 | "or"     { OR }
 | "and"    { AND }
 | "not"    { NOT }
 | "ite"    { ITE }
 | "if_then_else"  { IF_THEN_ELSE }
 | "iff"    { IFF }
 | "xor"    { XOR }
 | "implies"       { IMPLIES }
 | "let"    { LET }
 | "flet"   { FLET }
 | ">="     { GE }
 | "<="     { LE }
 | '='      { EQ }
 | '>'      { GT }
 | '<'      { LT }
 | '*'      { MUL }
 | '+'      { ADD }
 | '-'      { SUB }
 | "benchmark"     { BENCHMARK }
 | ":logic"        { LOGIC }
 | ":status"       { STATUS }
 | ":extrafuns"    { EXTRAFUNS }
 | ":extrapreds"   { EXTRAPREDS }
 | ":assumption"   { ASSUMPTION}
 | ":formula"      { FORMULA }
 | ":category"     { CATEGORY }
 | ":source"       { SOURCE }
 | ":difficulty"   { DIFFICULTY }
 | '~'      { TILDE }
 | num as s { NUM s }
 | id  as s { ID s }
 | comment as s { COMMENT s }
 | eof {EOF}
