all: src/rewriting/build/context.cmx src/rewriting/build/diagram.cmx src/rewriting/build/elogic.cmx src/rewriting/build/function.cmx src/rewriting/build/monad.cmx src/rewriting/build/parser.cmx src/rewriting/build/position.cmx src/rewriting/build/prelude.cmx src/rewriting/build/rewrite.cmx src/rewriting/build/rule.cmx src/rewriting/build/signature.cmx src/rewriting/build/substitution.cmx src/rewriting/build/term.cmx src/rewriting/build/trs.cmx src/rewriting/build/variable.cmx ;
include context.ml diagram.ml elogic.ml function.ml monad.ml parser.ml position.ml prelude.ml rewrite.ml rule.ml signature.ml substitution.ml term.ml trs.ml variable.ml
src/rewriting/%.cmx: ; @echo $@
%: ;
