type token =
  | ATTR of (string * string)
  | OPEN of (string)
  | CLOSEB of (string)
  | MOPEN of (string)
  | TEXT of (string)
  | MCLOSE
  | EOF
  | CLOSEE

open Parsing;;
let _ = parse_error;;
# 2 "src/ttt2/src/input/xmlParser.mly"
open Util.Xml;;
# 16 "src/ttt2/build/input/xmlParser.ml"
let yytransl_const = [|
  262 (* MCLOSE *);
    0 (* EOF *);
  263 (* CLOSEE *);
    0|]

let yytransl_block = [|
  257 (* ATTR *);
  258 (* OPEN *);
  259 (* CLOSEB *);
  260 (* MOPEN *);
  261 (* TEXT *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\004\000\004\000\003\000\003\000\005\000\
\005\000\006\000\000\000"

let yylen = "\002\000\
\003\000\004\000\000\000\002\000\000\000\003\000\006\000\002\000\
\000\000\000\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\011\000\000\000\000\000\000\000\000\000\
\000\000\004\000\000\000\000\000\001\000\002\000\000\000\006\000\
\000\000\000\000\008\000\000\000\007\000"

let yydgoto = "\002\000\
\004\000\005\000\017\000\007\000\018\000\000\000"

let yysindex = "\007\000\
\006\255\000\000\010\255\000\000\011\255\010\255\008\255\010\255\
\012\000\000\000\006\255\254\254\000\000\000\000\011\255\000\000\
\011\255\012\255\000\000\013\255\000\000"

let yyrindex = "\000\000\
\014\255\000\000\015\255\000\000\000\000\251\254\000\000\255\254\
\000\000\000\000\014\255\000\000\000\000\000\000\016\255\000\000\
\016\255\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\006\000\015\000\001\000\005\000\000\000"

let yytablesize = 22
let yytable = "\005\000\
\005\000\005\000\015\000\005\000\016\000\005\000\010\000\001\000\
\012\000\003\000\006\000\013\000\008\000\011\000\020\000\003\000\
\014\000\021\000\009\000\009\000\005\000\019\000"

let yycheck = "\005\001\
\006\001\007\001\005\001\005\001\007\001\007\001\006\000\001\000\
\008\000\004\001\001\001\000\000\002\001\006\001\003\001\002\001\
\011\000\005\001\003\001\005\000\006\001\017\000"

let yynames_const = "\
  MCLOSE\000\
  EOF\000\
  CLOSEE\000\
  "

let yynames_block = "\
  ATTR\000\
  OPEN\000\
  CLOSEB\000\
  MOPEN\000\
  TEXT\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'meta) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'node) in
    Obj.repr(
# 14 "src/ttt2/src/input/xmlParser.mly"
                   ( (_1, _2) )
# 93 "src/ttt2/build/input/xmlParser.ml"
               : Util.Xml.t))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'attrs) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'meta) in
    Obj.repr(
# 16 "src/ttt2/src/input/xmlParser.mly"
                              ( (_1, _2) :: _4 )
# 102 "src/ttt2/build/input/xmlParser.ml"
               : 'meta))
; (fun __caml_parser_env ->
    Obj.repr(
# 16 "src/ttt2/src/input/xmlParser.mly"
                                                   ( [] )
# 108 "src/ttt2/build/input/xmlParser.ml"
               : 'meta))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string * string) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'attrs) in
    Obj.repr(
# 18 "src/ttt2/src/input/xmlParser.mly"
                  ( _1 :: _2 )
# 116 "src/ttt2/build/input/xmlParser.ml"
               : 'attrs))
; (fun __caml_parser_env ->
    Obj.repr(
# 18 "src/ttt2/src/input/xmlParser.mly"
                                 ( [] )
# 122 "src/ttt2/build/input/xmlParser.ml"
               : 'attrs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'attrs) in
    Obj.repr(
# 21 "src/ttt2/src/input/xmlParser.mly"
                    ( mk_node _1 _2 [] None )
# 130 "src/ttt2/build/input/xmlParser.ml"
               : 'node))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'attrs) in
    let _3 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'nodes) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 22 "src/ttt2/src/input/xmlParser.mly"
                                    (
  let txt = if _3 = "" then None else Some _3 in
  if _1 = _5 && _6 = ""
    then mk_node _1 _2 _4 txt
    else raise Parse_error
)
# 147 "src/ttt2/build/input/xmlParser.ml"
               : 'node))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'node) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'nodes) in
    Obj.repr(
# 30 "src/ttt2/src/input/xmlParser.mly"
                  ( _1 :: _2 )
# 155 "src/ttt2/build/input/xmlParser.ml"
               : 'nodes))
; (fun __caml_parser_env ->
    Obj.repr(
# 30 "src/ttt2/src/input/xmlParser.mly"
                                 ( [] )
# 161 "src/ttt2/build/input/xmlParser.ml"
               : 'nodes))
; (fun __caml_parser_env ->
    Obj.repr(
# 32 "src/ttt2/src/input/xmlParser.mly"
      ( None )
# 167 "src/ttt2/build/input/xmlParser.ml"
               : 'text))
(* Entry doc *)
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
let doc (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Util.Xml.t)
;;
