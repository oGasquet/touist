all: src/automata/build/automaton.cmx src/automata/build/dependency.cmx src/automata/build/initial.cmx src/automata/build/lhs.cmx src/automata/build/monad.cmx src/automata/build/parser.cmx src/automata/build/path.cmx src/automata/build/prelude.cmx src/automata/build/reachability.cmx src/automata/build/rhs.cmx src/automata/build/state.cmx src/automata/build/status.cmx src/automata/build/substitution.cmx src/automata/build/term.cmx src/automata/build/transducer.cmx ;
include automaton.ml dependency.ml initial.ml lhs.ml monad.ml parser.ml path.ml prelude.ml reachability.ml rhs.ml state.ml status.ml substitution.ml term.ml transducer.ml
src/automata/%.cmx: ; @echo $@
%: ;
