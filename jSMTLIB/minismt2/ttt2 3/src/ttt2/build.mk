DIR   := src/ttt2
PACK  := Ttt2
DEP   := Util Parsec Rewriting Logic Automata Processors
GENERATED := \
  input/confParser.ml \
  input/confLexer.ml \
  input/xmlParser.ml \
  input/xmlLexer.ml \
  strategy/parser.ml \
  strategy/lexer.ml
# unused
#  input/srsParser.ml \
#  input/srsLexer.ml \
#  input/trsParser.ml \
#  input/trsLexer.ml
FILES := \
  input/wstParser.ml \
  input/confSyntax.ml \
  input/xmlInput.ml \
  output/xslt.ml \
  strategy/proof.ml \
  strategy/processor.ml \
  strategy/state.ml \
  strategy/monad.ml \
  strategy/transformation.ml \
  strategy/predicate.ml \
  strategy/modifier.ml \
  strategy/main.ml \
  strategy/nontermination.ml \
  strategy/status.ml \
  strategy/termination.ml \
  strategy/syntax.ml \
  kernel.ml \
  measure.ml \
  answer.ml \
  $(GENERATED)
# unused
#  input/trsSyntax.ml \
#  input/srsSyntax.ml

include mk/subdir.mk

XSL_FILES_Ttt2 := \
  cpf.xsl \
  html.xsl

# take care of generated files
$(BUILD)/%.ml: $(SRC)/%.mly | $$(dir $$@).dir
	$(OCAMLYACC) -b $(@:.ml=) $<
	rm $(@:.ml=.mli)

$(BUILD)/%.ml: $(SRC)/%.mll | $$(dir $$@).dir
	$(OCAMLLEX) -o $@ $<

.PRECIOUS: $(GENERATED:%=$(BUILD)/%)

# build ttt2
# packs to include in ttt2, in dependency order
PACKS_Ttt2 := Util Parsec Rewriting Logic Automata Processors Ttt2

LIBS_Ttt2 = $(foreach x,$(PACKS_Ttt2),$(LIB_$(x)))
LIBSO_Ttt2 = $(foreach x,$(PACKS_Ttt2),$(LIBO_$(x)))

# sadly, ld is very sensitive to the order of arguments, so adding the extra
# xslt.o file as a simple argument to ocamlopt.opt fails. Instead, we use
# -cclib, making sure that it comes before the libraries that it requires.
EXTRA_Ttt2 := $(BUILD_Ttt2)/xslt.o
LINK_Ttt2 := $(addprefix -cclib , $(EXTRA_Ttt2) $(XSLT_LIBS))

# prepare xsl files and combine into xslt.o
$(BUILD)/%.xsl.h: $(DIR)/%.xsl $(DIR)/strip-space.xsl $(DIR)/xxd.ml
	$(XSLTPROC) $(DIR_Ttt2)/strip-space.xsl $< | ocaml $(DIR_Ttt2)/xxd.ml $(notdir $<) > $@

$(BUILD)/xslt.o: $(SRC)/output/xslt.c $(patsubst %, $(BUILD)/%.h, $(XSL_FILES_Ttt2))
	$(OCAMLOPT) $(addprefix -ccopt , $(XSLT_INCS) -I $(BUILD_Ttt2) -o $@) -c $<

# using secondary expansion (the $$) is important: some LIB_Foo variables may
# not be defined yet the first time we get here
ttt2: $(DIR)/main.cmx $$(LIBS_Ttt2) $(EXTRA_Ttt2)
	$(OCAMLOPT) $(LINK) $(LINK_Logic) $(LINK_Ttt2) -o $@ $(LIBS_Ttt2) $<

ttt2.bytecode: $(DIR)/main.cmo $$(LIBSO_Ttt2) $(EXTRA_Ttt2)
	$(OCAMLC) $(LINK:.cmxa=.cma) $(subst .cmx,.cmo,$(LINK_Logic:.cmxa=.cma)) $(LINK_Ttt2:.cmxa=.cma) -o $@ $(LIBSO_Ttt2) $<

$(DIR)/main.cmx: $(DIR)/main.ml $(LIB_Ttt2)
	$(OCAMLOPT) -c -I $(DIR_Ttt2) -o $@ $<

$(DIR)/main.cmo: $(DIR)/main.ml $(LIBO_Ttt2)
	$(OCAMLC) -c -I $(DIR_Ttt2) -o $@ $<

measure: $(DIR)/measure.cmx $$(LIBS_Ttt2) $(EXTRA_Ttt2)
	$(OCAMLOPT) $(LINK) $(LINK_Logic) $(LINK_Ttt2) -o $@ $(LIBS_Ttt2) $<

$(DIR)/measure.cmx: $(DIR)/measure.ml $(LIB_Ttt2)
	$(OCAMLOPT) -c -I $(DIR_Ttt2) -o $@ $<

# extra housekeeping
clean-$(PACK)::
	rm -f $(foreach x,$(addprefix $(DIR_$(PACK))/,main measure),$(addprefix $x,.cmx .cmo .cmi .o))

distclean-$(PACK)::
	rm -rf ttt2 ttt2.bytecode measure

# HACK:
# The build system overapproximates dependencies, which results in circular
# dependencies. Here we identify some false positives to break cycles:

# - uses of Monad from Util
# - uses of Modifier, Nontermination, Termination, Transformation from Processors
$(DEPDIR)/strategy/processor.ml: BLACKLIST := Monad Modifier Nontermination Termination Transformation
$(DEPDIR)/strategy/proof.ml: BLACKLIST := Monad Transformation
$(DEPDIR)/strategy/state.ml: BLACKLIST := Monad
$(DEPDIR)/input/%: BLACKLIST := Monad
