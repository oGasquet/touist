/* $Id: parser2.mly,v 1.1 2010/06/21 12:15:40 hzankl Exp $

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
 module SMT = SmtFormula;;
 let set_logic _ x = x;;
 let add_extrapreds _ x = x;;
 let add_assertion _ x = x;;
 let set_info s x = SmtFormula.add_info s x;;
 let add_declaration (var,typ) x = match typ with
  | "Bool" -> SmtFormula.add_extrapreds [var] x
  | _ -> SmtFormula.add_extrafuns [(var,typ)] x
 let add_assertion ass x = SmtFormula.add_assumptions [ass] x;;
 let ua (k,v) a = match v with 
  | Left  v -> SMT.sub_aa (SMT.Vara k) v a 
  | Right v -> SMT.sub_ba (SMT.Varb k) v a;;
 let ub (k,v) b = match v with 
  | Left  v -> SMT.sub_ab (SMT.Vara k) v b 
  | Right v -> SMT.sub_bb (SMT.Varb k) v b;;
 let unfold_a bs x = List.fold_right ua bs x;; 
 let unfold_b bs x = List.fold_right ub bs x;;
%}

/***DECLARATIONS***/ 
%token <string> ID 
%token <string> NUM
%token <string> COMMENT KEYWORD
%token TILDE
%token ADD SUB MUL ITE
%token GE GT EQ LE LT
%token AND OR NOT TOP BOT IF_THEN_ELSE
%token IFF IMPLIES XOR
%token LET 
%token LPAREN RPAREN 
%token LOGIC DECLARE ASSERT INFO CHECKSAT EXIT
%token EOF
%start parse
%type <SmtFormula.smt> parse

/***RULES***/
%%
parse:
 all EOF {$1}
;

all: 
 | logic input {SmtFormula.set_logic $1 $2}

input:
 | {SmtFormula.add_formula Ops.top SmtFormula.empty}
 | info input {set_info $1 $2}
 | declare input {add_declaration $1 $2}
 | assertion input {add_assertion $1 $2}
 | command input {$2}
 | {failwith "error when parsing input"}
;

logic:
 | LPAREN LOGIC ID RPAREN {$3};
 | {failwith "error when parsing logic"}

info: 
 | LPAREN INFO KEYWORD expr RPAREN {Format.sprintf "(:set-info %s %s)" $3 $4}
 | {failwith "error when parsing info"}
;

expr:
 | NUM {$1}
 | ID {$1}
;

declare:
 | LPAREN DECLARE ID args ID RPAREN {($3,$5)};
 | {failwith "error when parsing declaration"}

args:
 | LPAREN RPAREN {()}

assertion:
 | LPAREN ASSERT bformula RPAREN {$3}
 | {failwith "error when parsing assert"}

command:    
 | LPAREN CHECKSAT RPAREN {()};
 | LPAREN EXIT RPAREN     {()};

var  : ID {$1}
avar : ID {SmtFormula.Vara $1}
bvar : ID {SmtFormula.Varb $1}

aformula:
 | LPAREN aformula RPAREN {$2}
 | TILDE aformula         {Ops.(<->) (Ops.const Int64.zero) $2}
 | NUM       {Ops.const (Int64.of_string $1)}
 | ADD alist {Ops.big_add $2}
 | SUB alist {Ops.big_sub $2}
 | MUL alist {Ops.big_mul $2}
 | ITE bformula aformula aformula  {Ops.ite $2 $3 $4}
 | LET LPAREN bindinglist RPAREN aformula  {unfold_a $3 $5}
 /*| FLET LPAREN bvar bformula RPAREN aformula {SmtFormula.sub_ba $3 $4 $6}*/
 | avar      {$1}
;

bindinglist:
 | LPAREN var aformula RPAREN bindinglist {($2,Left $3)::$5}
 | LPAREN var bformula RPAREN bindinglist {($2,Right $3)::$5}
 | {[]}
;


alist : 
 | aformula       {[$1]}
 | aformula alist {$1::$2}
;

bformula: 
 | LPAREN bformula RPAREN {$2}
 | bvar                   {$1}
 | TOP                    {SmtFormula.Top}
 | BOT                    {SmtFormula.Bot}
 | LPAREN NOT bformula RPAREN {SmtFormula.Not $3}
 | LPAREN OR blist RPAREN  {Ops.big_or $3}
 | LPAREN AND blist RPAREN {Ops.big_and $3}
 | LPAREN IFF blist RPAREN {Ops.big_iff $3}
 | LPAREN XOR blist RPAREN {SmtFormula.Not (Ops.big_iff $3)}
 | LPAREN IMPLIES bformula bformula RPAREN {SmtFormula.Implies ($3,$4)}
 | LPAREN GT aformula aformula RPAREN {SmtFormula.Gt ($3,$4)}
 | LPAREN GE aformula aformula RPAREN {SmtFormula.Ge ($3,$4)}
 | LPAREN LE aformula aformula RPAREN {SmtFormula.Ge ($4,$3)}
 | LPAREN LT aformula aformula RPAREN {SmtFormula.Gt ($4,$3)}
 | LPAREN EQ aformula aformula RPAREN {SmtFormula.Eq ($3,$4)}
 | ITE bformula bformula bformula  
  {Ops.(<|>) (Ops.(<&>) $2 $3) (Ops.(<&>) (Ops.neg $2) $4)}
 | LET LPAREN bindinglist RPAREN bformula  {unfold_b $3 $5}
 /*| LET LPAREN avar aformula RPAREN bformula  {SmtFormula.sub_ab $3 $4 $6}*/
 /*| FLET LPAREN bvar bformula RPAREN bformula {SmtFormula.sub_bb $3 $4
  * $6}*/
 | IF_THEN_ELSE bformula bformula bformula 
  {Ops.(<|>) (Ops.(<&>) $2 $3) (Ops.(<&>) (Ops.neg $2) $4)}
;


blist :
 | bformula       {[$1]}
 | bformula blist {$1::$2}

/***TRAILER***/ 
%%
