DIR   := src/automata
PACK  := Automata
DEP   := Util Parsec Rewriting
FILES := \
  automaton.ml \
  dependency.ml \
  initial.ml \
  lhs.ml \
  monad.ml \
  parser.ml \
  path.ml \
  prelude.ml \
  reachability.ml \
  rhs.ml \
  state.ml \
  status.ml \
  substitution.ml \
  term.ml \
  transducer.ml

include mk/subdir.mk

INCLUDES_Automata=$(addprefix -I src/,$(call map,lower,$(DEP_Automata) Automata))
LIBS_Automata = $(foreach x,$(DEP_Automata) Automata,$(LIB_$(x)))

$(DIR)/test.cmx: $(DIR)/test.ml $(LIB_Automata) $(DIR)/build.mk
	$(OCAMLOPT) -c $(INCLUDES_Automata) -o $@ $<

test-automata: $(DIR)/test.cmx $(LIB_Automata)
	$(OCAMLOPT) $(LINK) $(INCLUDES_Automata) $(LIBS_Automata) $<
