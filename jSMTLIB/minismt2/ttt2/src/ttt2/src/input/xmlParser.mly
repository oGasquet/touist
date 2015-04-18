%{
open Util.Xml;;
%}

%token <string * string> ATTR
%token <string> OPEN CLOSEB MOPEN TEXT
%token MCLOSE EOF CLOSEE

%type <Util.Xml.t> doc
%start doc

%%

doc: meta node EOF { ($1, $2) };

meta: MOPEN attrs MCLOSE meta { ($1, $2) :: $4 } | { [] };

attrs: ATTR attrs { $1 :: $2 } | { [] };

node:
  OPEN attrs CLOSEE { mk_node $1 $2 [] None }
| OPEN attrs TEXT nodes CLOSEB TEXT {
  let txt = if $3 = "" then None else Some $3 in
  if $1 = $5 && $6 = ""
    then mk_node $1 $2 $4 txt
    else raise Parse_error
}
;

nodes: node nodes { $1 :: $2 } | { [] };

text: { None };

%%
