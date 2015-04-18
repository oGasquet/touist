(* $Id: lexer2.mll,v 1.1 2010/06/21 12:15:40 hzankl Exp $ *)

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
 open Parser2;;
}

let digit = ['0'-'9']
let letter = ['A'-'Z''a'-'z']
let special = ['~''!''@''#''$''%''^''&''*''_''-''+''=''<''>''.''?''"']
let rest    = ['|''\\'':'';''\\''('')']
let space = [' ''\t''\n''\r']

let comment = ';' [^'\n'] '\n'
let numeral = '0' | ['1'-'9']digit*
let decimal = numeral".""0"*numeral
let hexadecimal = "#x"(['A'-'F'] | digit)*
let binary = "#b"['0'-'1']*
let string = '"'[^'"']'"'
let symbol = (letter | special)(letter | digit | special)* | ("|"[^'|']*"|")
let keyword = ":"(letter | digit | special)+

let spec_const = numeral | decimal | hexadecimal | binary | string
(* let s_expr = spec_const | symbol | keyword | "("s_expr*")" *)
(* let identifier = symbol | '('_ symbol numeral* ')' *)
(*  *)
(* let attribute_value = spec_const | symbol | '('s_expr* ')' *)
(* let attribute = keyword | keyword s_expr *)
(* let sort = "Bool" | identifier | '('identifier sort+')' *)

(* translate into tokens *)
rule token = parse
 | space {token lexbuf}
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
 (*| "flet"   { FLET }*)
 | ">="     { GE }
 | "<="     { LE }
 | '='      { EQ }
 | '>'      { GT }
 | '<'      { LT }
 | '*'      { MUL }
 | '+'      { ADD }
 | '-'      { SUB }
 | "set-logic"        { LOGIC }
 | "assert"   { ASSERT }
 | "declare-fun"    { DECLARE }
 | "check-sat"   { CHECKSAT }
 | "set-info"   { INFO }
 | "exit"   { EXIT}
 | '~'      { TILDE }
 | spec_const as s { NUM s }
 | symbol as s { ID s }
 | comment as s { COMMENT s }
 | keyword as s { KEYWORD s }
 | eof as s { EOF }
