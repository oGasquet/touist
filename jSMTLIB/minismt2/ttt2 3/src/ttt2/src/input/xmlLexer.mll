{
open XmlParser;;
}

let ws = [' ''\t''\n''\r'] (*white space*)
let s  = ws* (*arbitrary space*)
let id = ['a'-'z''A'-'Z''-'':']+ (*identifier*)
let no = [^'<']

rule token =
  parse
    | "<!--"              s { comment lexbuf }
    | "<"  s (id as tag)  s { OPEN tag }
    | "</" s (id as tag)  s { CLOSEB tag }
    | "<?" s (id as tag)  s { MOPEN tag }
    | "/>"                s { CLOSEE }
    | "?>"                s { MCLOSE }
    | ">"  s (no* as txt) s { TEXT txt }
    | (id as k) s '=' s '"'([^'"']* as v)'"' { ATTR (k, v) }
    | _ { token lexbuf }
    | eof { EOF }
and comment =
  parse
    | "-->" { token lexbuf }
    | _ { comment lexbuf }
