/* $Id: parser.mly,v 1.13 2010/06/21 12:15:40 hzankl Exp $

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
 let set_benchmark _ x = x;;
 let set_status _ x = x;;
 let set_logic _ x = x;;
 let add_extrapreds _ x = x;;
 let add_extrafuns _ x = x;;
 let add_assumptions _ x = x;;
 let add_formula _ x = x;;

 let set_category _ x = x;;
 let set_source _ x = x;;
%}

/***DECLARATIONS***/ 
%token <string> ID
%token <string> NUM
%token <string> COMMENT
%token TILDE
%token ADD SUB MUL ITE
%token GE GT EQ LE LT
%token AND OR NOT TOP BOT IF_THEN_ELSE
%token IFF IMPLIES XOR
%token LET FLET
%token LPAREN RPAREN 
%token BENCHMARK LOGIC STATUS SOURCE CATEGORY DIFFICULTY
%token EXTRAFUNS EXTRAPREDS ASSUMPTION FORMULA
%token EOF
%start parse
%type <SmtFormula.smt> parse

/***RULES***/
%%
parse:
 all EOF {$1}
;

all: LPAREN benchmark input RPAREN 
    {set_benchmark $2 $3}

input:
 | {SmtFormula.empty}
 | status input {SmtFormula.set_status $1 $2}
 | logic input {SmtFormula.set_logic $1 $2}
 | difficulty input {SmtFormula.set_difficulty $1 $2}
 | source input {SmtFormula.set_source $1 $2}
 | category input {SmtFormula.set_category $1 $2}
 | extrafuns input {SmtFormula.add_extrafuns $1 $2}
 | extrapreds input {SmtFormula.add_extrapreds $1 $2}
 | assumptions input {SmtFormula.add_assumptions $1 $2}
 | formula input {SmtFormula.add_formula $1 $2}
;

benchmark: 
 |              {"unknown"}
 | BENCHMARK ID {$2}
;

difficulty:
 |               {"unknown"}
 | DIFFICULTY COMMENT {$2};

logic:
 |          {"unknown"}
 | LOGIC ID {$2};

status:    
 |           {"unknown"} 
 | STATUS ID {$2};

source:    
 |           {"unknown"} 
 | SOURCE COMMENT {$2};

category:    
 |           {"unknown"} 
 | CATEGORY COMMENT {$2};

extrafuns: 
 |                               {[]}
 | EXTRAFUNS LPAREN flist RPAREN {$3};

flist: 
 |                           {[]}
 | LPAREN ID ID RPAREN flist {($2,$3)::$5}

extrapreds: 
 |                                {[]}
 | EXTRAPREDS LPAREN plist RPAREN {$3};

plist: 
 |                        {[]}
 | LPAREN ID RPAREN plist {$2::$4}

assumptions: 
 |                                 {[]}
 | ASSUMPTION bformula assumptions {$2::$3}
;

formula : FORMULA bformula {$2}

aformula:
 | LPAREN aformula RPAREN {$2}
 | TILDE aformula         {Ops.(<->) (Ops.const Int64.zero) $2}
 | NUM       {Ops.const (Int64.of_string $1)}
 | ADD alist {Ops.big_add $2}
 | SUB alist {Ops.big_sub $2}
 | MUL alist {Ops.big_mul $2}
 | ITE bformula aformula aformula            {Ops.ite $2 $3 $4}
 /*| LET LPAREN avar aformula RPAREN aformula  {SmtFormula.sub_aa $3 $4 $6}*/
 /*| FLET LPAREN bvar bformula RPAREN aformula {SmtFormula.sub_ba $3 $4 $6}*/
 | avar      {$1}
;

var  : ID {$1}
avar : ID {SmtFormula.Vara $1}

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
 /*| LET LPAREN var aformula RPAREN bformula * * {SmtFormula.Let($3,$4,$6)}*/
 | LET LPAREN avar aformula RPAREN bformula  {SmtFormula.sub_ab $3 $4 $6}
 | FLET LPAREN bvar bformula RPAREN bformula {SmtFormula.sub_bb $3 $4 $6}
 | IF_THEN_ELSE bformula bformula bformula 
  {Ops.(<|>) (Ops.(<&>) $2 $3) (Ops.(<&>) (Ops.neg $2) $4)}
;

bvar : ID {SmtFormula.Varb $1}

blist :
 | bformula       {[$1]}
 | bformula blist {$1::$2}

/***TRAILER***/ 
%%
