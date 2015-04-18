DIR   := src/logic
PACK  := Logic
DEP   := Util #Parsec #Rewriting
FILES := \
  a.ml \
  ass.ml \
  assignment.ml \
  binInt.ml \
  binMinf.ml \
  binNat.ml \
  binNumber.ml \
  binRat.ml \
  binReal.ml \
  binType.ml \
  formula.ml \
  integer.ml \
  minf.ml \
  miniSmt.ml \
  monad.ml \
  number.ml \
  operators.ml \
  p.ml \
  pss.ml \
  rational.ml \
  real.ml \
  solver.ml \
  state.ml

FILES += $(if $(DISABLE_MiniSat),dummy/miniSat.ml,miniSat.ml)
FILES += $(if $(DISABLE_MiniSatP),dummy/miniSatP.ml,miniSatP.ml)
FILES += $(if $(DISABLE_Yices),dummy/yices.ml,yices.ml)
FILES += $(if $(DISABLE_PicoSat),dummy/picoSat.ml,picoSat.ml)
FILES += $(if $(DISABLE_Gpw),dummy/gpw.ml,gpw.ml)

include mk/subdir.mk

# Logic needs extra flags when linking
LINK_Logic :=

ifndef DISABLE_MiniSat
LOGICLIBS += minisat
LOGICOBJS += interface
LINK_Logic += -I $(BUILD)-lib/minisat
endif

ifndef DISABLE_MiniSatP
LOGICLIBS += minisatp
LOGICOBJS += minisatPlus
LINK_Logic += -I $(BUILD)-lib/minisat+
endif

ifndef DISABLE_Yices
LOGICLIBS += yices
LOGICOBJS += yinterface
LINK_Logic += -I $(BUILD)-lib/yices
endif

ifndef DISABLE_PicoSat
LOGICLIBS += picosat
LOGICOBJS += picosatInterface
LINK_Logic += -I $(BUILD)-lib/picosat
endif

ifndef DISABLE_Gpw
LOGICLIBS += gpw
LOGICOBJS += gpwSolver
LINK_Logic += -I $(BUILD)-lib/gpw -cclib -lgmp
endif

LINK_Logic += $(LOGICLIBS:=.cmxa) $(LOGICOBJS:=.cmx)

# minisat
$(BUILD)/miniSat.cmx $(BUILD)/miniSat.cmo: $(BUILD)/interface.cmi

$(BUILD)-lib/interface.cmi: $(BUILD)-lib/.dir
	cp -r $(SRC_Logic)/minisat $(BUILD_Logic)-lib
	$(MAKE) -C $(BUILD_Logic)-lib/minisat
	cp $(BUILD_Logic)-lib/minisat/interface.cmi $@

# minisat+
$(BUILD)/miniSatP.cmx $(BUILD)/miniSatP.cmo: $(BUILD)/minisatPlus.cmi

$(BUILD)-lib/minisatPlus.cmi: $(BUILD)-lib/.dir
	cp -r $(SRC_Logic)/minisat+ $(BUILD_Logic)-lib
	$(MAKE) -C $(BUILD_Logic)-lib/minisat+
	cp $(BUILD_Logic)-lib/minisat+/minisatPlus.cmi $@

# yices
$(BUILD)/yices.cmx $(BUILD)/yices.cmo: $(BUILD)/yinterface.cmi

$(BUILD)-lib/yinterface.cmi: $(BUILD)-lib/.dir
	cp -r $(SRC_Logic)/yices $(BUILD_Logic)-lib
	$(MAKE) -C $(BUILD_Logic)-lib/yices EXTRA_LINK="-cclib -L$(shell pwd)/$(BUILD_Logic)-lib/yices/$(BITS)bit/lib"
	cp $(BUILD_Logic)-lib/yices/yinterface.cmi $@

# picosat
$(BUILD)/picoSat.cmx $(BUILD)/picoSat.cmo: $(BUILD)/picosatInterface.cmi

$(BUILD)-lib/picosatInterface.cmi: $(BUILD)-lib/.dir
	cp -r $(SRC_Logic)/picosat $(BUILD_Logic)-lib
	$(MAKE) -C $(BUILD_Logic)-lib/picosat
	cp $(BUILD_Logic)-lib/picosat/picosatInterface.cmi $@

# gpw
$(BUILD)/gpw.cmx $(BUILD)/gpw.cmo: $(BUILD)/gpwSolver.cmi

$(BUILD)-lib/gpwSolver.cmi: $(BUILD)-lib/.dir
	cp -r $(SRC_Logic)/gpw $(BUILD_Logic)-lib
	$(MAKE) -C $(BUILD_Logic)-lib/gpw
	cp $(BUILD_Logic)-lib/gpw/gpwSolver.cmi $@

$(BUILD)/%.cmi: $(BUILD)-lib/%.cmi
	cp $< $@

distclean::
	rm -rf $(BUILD_Logic)-lib
