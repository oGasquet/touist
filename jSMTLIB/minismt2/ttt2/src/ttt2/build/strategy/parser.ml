type token =
  | AND
  | COLON
  | COMMA
  | ELSE
  | EOF
  | EXCLAMATION_MARK
  | GREATER
  | IF
  | LEFT_BRACE
  | LEFT_BRACKET
  | LEFT_PAREN
  | PERCENT
  | PIPE
  | PLUS
  | QUESTION_MARK
  | RIGHT_BRACE
  | RIGHT_BRACKET
  | RIGHT_PAREN
  | SEMICOLON
  | SMALLER
  | STAR
  | THEN
  | FLOAT of (float)
  | ID of (string)
  | INT of (int)

open Parsing;;
let _ = parse_error;;
# 22 "src/ttt2/src/strategy/parser.mly"
(*** OPENS ********************************************************************)
open Syntax;;
# 34 "src/ttt2/build/strategy/parser.ml"
let yytransl_const = [|
  257 (* AND *);
  258 (* COLON *);
  259 (* COMMA *);
  260 (* ELSE *);
    0 (* EOF *);
  261 (* EXCLAMATION_MARK *);
  262 (* GREATER *);
  263 (* IF *);
  264 (* LEFT_BRACE *);
  265 (* LEFT_BRACKET *);
  266 (* LEFT_PAREN *);
  267 (* PERCENT *);
  268 (* PIPE *);
  269 (* PLUS *);
  270 (* QUESTION_MARK *);
  271 (* RIGHT_BRACE *);
  272 (* RIGHT_BRACKET *);
  273 (* RIGHT_PAREN *);
  274 (* SEMICOLON *);
  275 (* SMALLER *);
  276 (* STAR *);
  277 (* THEN *);
    0|]

let yytransl_block = [|
  278 (* FLOAT *);
  279 (* ID *);
  280 (* INT *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\003\000\003\000\003\000\003\000\003\000\002\000\002\000\
\002\000\002\000\000\000"

let yylen = "\002\000\
\002\000\002\000\002\000\004\000\004\000\005\000\002\000\002\000\
\002\000\003\000\005\000\005\000\003\000\003\000\004\000\006\000\
\003\000\002\000\002\000\003\000\003\000\003\000\000\000\002\000\
\002\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\001\000\003\000\000\000\002\000\000\000\009\000\007\000\000\000\
\008\000\000\000\019\000\000\000\018\000\000\000\000\000\000\000\
\000\000\017\000\026\000\024\000\025\000\000\000\000\000\000\000\
\000\000\000\000\010\000\022\000\020\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\006\000\012\000\011\000\000\000"

let yydgoto = "\002\000\
\007\000\017\000\011\000"

let yysindex = "\006\000\
\039\255\000\000\016\255\039\255\039\255\247\254\097\255\016\255\
\016\255\247\254\011\255\069\255\083\255\247\254\247\254\247\254\
\000\000\000\000\102\255\000\000\056\255\000\000\000\000\039\255\
\000\000\254\254\000\000\074\255\000\000\016\255\016\255\039\255\
\001\255\000\000\000\000\000\000\000\000\021\255\027\255\039\255\
\109\255\020\255\000\000\000\000\000\000\053\255\047\255\247\254\
\028\255\035\255\109\255\039\255\000\000\000\000\000\000\097\255"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\053\000\069\000\000\000\
\000\000\255\254\000\000\000\000\000\000\035\000\035\000\035\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\072\000\057\000\000\000\000\000\000\000\024\255\000\000\053\000\
\001\000\017\000\073\000\000\000\000\000\000\000\000\000\076\000"

let yygindex = "\000\000\
\254\255\250\255\253\255"

let yytablesize = 349
let yytable = "\023\000\
\005\000\012\000\013\000\029\000\027\000\028\000\001\000\035\000\
\036\000\037\000\023\000\030\000\014\000\015\000\016\000\023\000\
\004\000\043\000\041\000\023\000\008\000\042\000\031\000\048\000\
\018\000\009\000\045\000\046\000\019\000\047\000\020\000\032\000\
\022\000\023\000\023\000\021\000\049\000\051\000\010\000\025\000\
\021\000\053\000\050\000\026\000\021\000\003\000\004\000\054\000\
\005\000\056\000\052\000\018\000\023\000\030\000\055\000\019\000\
\013\000\020\000\021\000\022\000\023\000\006\000\003\000\004\000\
\024\000\005\000\025\000\040\000\027\000\000\000\026\000\014\000\
\015\000\018\000\030\000\016\000\000\000\019\000\006\000\020\000\
\021\000\022\000\023\000\033\000\000\000\031\000\024\000\018\000\
\025\000\000\000\044\000\019\000\026\000\020\000\021\000\022\000\
\023\000\000\000\000\000\034\000\024\000\018\000\025\000\000\000\
\000\000\019\000\026\000\020\000\021\000\022\000\023\000\000\000\
\000\000\018\000\024\000\000\000\025\000\019\000\000\000\020\000\
\026\000\022\000\023\000\038\000\000\000\039\000\024\000\000\000\
\025\000\000\000\000\000\000\000\026\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\005\000\005\000\000\000\000\000\
\000\000\005\000\000\000\005\000\005\000\005\000\005\000\005\000\
\000\000\005\000\005\000\000\000\004\000\004\000\000\000\000\000\
\005\000\004\000\000\000\004\000\004\000\004\000\004\000\004\000\
\000\000\004\000\004\000\023\000\000\000\000\000\023\000\023\000\
\004\000\000\000\000\000\023\000\000\000\023\000\023\000\023\000\
\023\000\023\000\000\000\023\000\023\000\000\000\023\000\023\000\
\023\000\023\000\000\000\000\000\013\000\023\000\000\000\023\000\
\023\000\023\000\023\000\023\000\013\000\023\000\023\000\013\000\
\023\000\013\000\013\000\014\000\015\000\000\000\000\000\016\000\
\000\000\000\000\000\000\014\000\015\000\000\000\014\000\015\000\
\014\000\015\000\016\000\000\000\016\000"

let yycheck = "\001\001\
\000\000\004\000\005\000\010\000\008\000\009\000\001\000\014\000\
\015\000\016\000\012\001\001\001\022\001\023\001\024\001\017\001\
\000\000\020\001\021\000\021\001\005\001\024\000\012\001\023\001\
\005\001\010\001\030\000\031\000\009\001\032\000\011\001\021\001\
\013\001\014\001\000\000\012\001\016\001\040\000\023\001\020\001\
\017\001\048\000\016\001\024\001\021\001\007\001\008\001\020\001\
\010\001\052\000\004\001\005\001\000\000\001\001\020\001\009\001\
\000\000\011\001\012\001\013\001\014\001\023\001\007\001\008\001\
\018\001\010\001\020\001\012\001\000\000\255\255\024\001\000\000\
\000\000\005\001\001\001\000\000\255\255\009\001\023\001\011\001\
\012\001\013\001\014\001\015\001\255\255\012\001\018\001\005\001\
\020\001\255\255\017\001\009\001\024\001\011\001\012\001\013\001\
\014\001\255\255\255\255\017\001\018\001\005\001\020\001\255\255\
\255\255\009\001\024\001\011\001\012\001\013\001\014\001\255\255\
\255\255\005\001\018\001\255\255\020\001\009\001\255\255\011\001\
\024\001\013\001\014\001\022\001\255\255\024\001\018\001\255\255\
\020\001\255\255\255\255\255\255\024\001\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\004\001\005\001\255\255\255\255\
\255\255\009\001\255\255\011\001\012\001\013\001\014\001\015\001\
\255\255\017\001\018\001\255\255\004\001\005\001\255\255\255\255\
\024\001\009\001\255\255\011\001\012\001\013\001\014\001\015\001\
\255\255\017\001\018\001\001\001\255\255\255\255\004\001\005\001\
\024\001\255\255\255\255\009\001\255\255\011\001\012\001\013\001\
\014\001\015\001\255\255\017\001\018\001\255\255\020\001\021\001\
\004\001\005\001\255\255\255\255\004\001\009\001\255\255\011\001\
\012\001\013\001\014\001\015\001\012\001\017\001\018\001\015\001\
\020\001\017\001\018\001\004\001\004\001\255\255\255\255\004\001\
\255\255\255\255\255\255\012\001\012\001\255\255\015\001\015\001\
\017\001\017\001\015\001\255\255\017\001"

let yynames_const = "\
  AND\000\
  COLON\000\
  COMMA\000\
  ELSE\000\
  EOF\000\
  EXCLAMATION_MARK\000\
  GREATER\000\
  IF\000\
  LEFT_BRACE\000\
  LEFT_BRACKET\000\
  LEFT_PAREN\000\
  PERCENT\000\
  PIPE\000\
  PLUS\000\
  QUESTION_MARK\000\
  RIGHT_BRACE\000\
  RIGHT_BRACKET\000\
  RIGHT_PAREN\000\
  SEMICOLON\000\
  SMALLER\000\
  STAR\000\
  THEN\000\
  "

let yynames_block = "\
  FLOAT\000\
  ID\000\
  INT\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'args) in
    Obj.repr(
# 67 "src/ttt2/src/strategy/parser.mly"
           (Strategy (_1,_2))
# 243 "src/ttt2/build/strategy/parser.ml"
               : Syntax.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Syntax.t) in
    Obj.repr(
# 69 "src/ttt2/src/strategy/parser.mly"
                    (Stop _1)
# 250 "src/ttt2/build/strategy/parser.ml"
               : Syntax.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Syntax.t) in
    Obj.repr(
# 70 "src/ttt2/src/strategy/parser.mly"
                             (Strict _1)
# 257 "src/ttt2/build/strategy/parser.ml"
               : Syntax.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : Syntax.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : int) in
    Obj.repr(
# 71 "src/ttt2/src/strategy/parser.mly"
                                           (Timed (float_of_int _3,_1))
# 265 "src/ttt2/build/strategy/parser.ml"
               : Syntax.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : Syntax.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : float) in
    Obj.repr(
# 72 "src/ttt2/src/strategy/parser.mly"
                                             (Timed (_3,_1))
# 273 "src/ttt2/build/strategy/parser.ml"
               : Syntax.t))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : Syntax.t) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'args) in
    Obj.repr(
# 73 "src/ttt2/src/strategy/parser.mly"
                                           (Modify (_2,(_4,_5)))
# 282 "src/ttt2/build/strategy/parser.ml"
               : Syntax.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Syntax.t) in
    Obj.repr(
# 75 "src/ttt2/src/strategy/parser.mly"
                          (Optional _1)
# 289 "src/ttt2/build/strategy/parser.ml"
               : Syntax.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Syntax.t) in
    Obj.repr(
# 76 "src/ttt2/src/strategy/parser.mly"
                 (Iterate _1)
# 296 "src/ttt2/build/strategy/parser.ml"
               : Syntax.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Syntax.t) in
    Obj.repr(
# 77 "src/ttt2/src/strategy/parser.mly"
                 (Repeat _1)
# 303 "src/ttt2/build/strategy/parser.ml"
               : Syntax.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Syntax.t) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : int) in
    Obj.repr(
# 78 "src/ttt2/src/strategy/parser.mly"
                     (Replicate (_2,_1))
# 311 "src/ttt2/build/strategy/parser.ml"
               : Syntax.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : Syntax.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : int) in
    Obj.repr(
# 80 "src/ttt2/src/strategy/parser.mly"
  (Iterate_timed (float_of_int _3,_1))
# 319 "src/ttt2/build/strategy/parser.ml"
               : Syntax.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : Syntax.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : float) in
    Obj.repr(
# 81 "src/ttt2/src/strategy/parser.mly"
                                                  (Iterate_timed (_3,_1))
# 327 "src/ttt2/build/strategy/parser.ml"
               : Syntax.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Syntax.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Syntax.t) in
    Obj.repr(
# 83 "src/ttt2/src/strategy/parser.mly"
                               (Combine (_1,_3))
# 335 "src/ttt2/build/strategy/parser.ml"
               : Syntax.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Syntax.t) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Syntax.t) in
    Obj.repr(
# 84 "src/ttt2/src/strategy/parser.mly"
                          (Choose (_1,_3))
# 343 "src/ttt2/build/strategy/parser.ml"
               : Syntax.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : Syntax.t) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Syntax.t) in
    Obj.repr(
# 85 "src/ttt2/src/strategy/parser.mly"
                               (Parallel (_1,_4))
# 351 "src/ttt2/build/strategy/parser.ml"
               : Syntax.t))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'condition) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : Syntax.t) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : Syntax.t) in
    Obj.repr(
# 86 "src/ttt2/src/strategy/parser.mly"
                                            (Condition (_2,_4,_6))
# 360 "src/ttt2/build/strategy/parser.ml"
               : Syntax.t))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Syntax.t) in
    Obj.repr(
# 88 "src/ttt2/src/strategy/parser.mly"
                                   (_2)
# 367 "src/ttt2/build/strategy/parser.ml"
               : Syntax.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'args) in
    Obj.repr(
# 92 "src/ttt2/src/strategy/parser.mly"
           (Atom (_1,_2))
# 375 "src/ttt2/build/strategy/parser.ml"
               : 'condition))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'condition) in
    Obj.repr(
# 93 "src/ttt2/src/strategy/parser.mly"
                              (Not _2)
# 382 "src/ttt2/build/strategy/parser.ml"
               : 'condition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'condition) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'condition) in
    Obj.repr(
# 94 "src/ttt2/src/strategy/parser.mly"
                           (And (_1,_3))
# 390 "src/ttt2/build/strategy/parser.ml"
               : 'condition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'condition) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'condition) in
    Obj.repr(
# 95 "src/ttt2/src/strategy/parser.mly"
                            (Or (_1,_3))
# 398 "src/ttt2/build/strategy/parser.ml"
               : 'condition))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'condition) in
    Obj.repr(
# 96 "src/ttt2/src/strategy/parser.mly"
                                    (_2)
# 405 "src/ttt2/build/strategy/parser.ml"
               : 'condition))
; (fun __caml_parser_env ->
    Obj.repr(
# 100 "src/ttt2/src/strategy/parser.mly"
   ([])
# 411 "src/ttt2/build/strategy/parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'args) in
    Obj.repr(
# 101 "src/ttt2/src/strategy/parser.mly"
           (_1 :: _2)
# 419 "src/ttt2/build/strategy/parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : int) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'args) in
    Obj.repr(
# 102 "src/ttt2/src/strategy/parser.mly"
            (string_of_int _1 :: _2)
# 427 "src/ttt2/build/strategy/parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : float) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'args) in
    Obj.repr(
# 103 "src/ttt2/src/strategy/parser.mly"
              (string_of_float _1 :: _2)
# 435 "src/ttt2/build/strategy/parser.ml"
               : 'args))
(* Entry strategy *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let strategy (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Syntax.t)
;;
