include mk/toplevel-util.mk

SHELL     := bash
OCAML     := $(call check-opt,ocaml)
OCAMLOPT  := $(call check-opt,ocamlopt) -g
OCAMLC    := $(call check-opt,ocamlc)
OCAMLTOP  := $(call check-opt,ocamlmktop)
OCAMLDEP  := $(call check-opt,ocamldep)
OCAMLYACC := $(call check-opt,ocamlyacc)
OCAMLLEX  := $(call check-opt,ocamllex)
OCAMLDOC  := $(call check-opt,ocamldoc)
XSLTPROC  := xsltproc
PERL      := perl
STATIC    :=
XSLT_VER  := $(shell pkg-config --modversion libxslt)
XSLT_LIBS := $(shell pkg-config --libs --static libxslt) \
  $(if $(STATIC),-lpthread -llzma,)
XSLT_INCS := $(shell pkg-config --cflags libxslt)

DISABLE_Yices=1

# other programs:
# echo, cp, chmod, rm, mkdir

# sanity check -- pkg-config
ifeq ($(shell pkg-config --version),)
  $(warning *** Could not find pkg-config.)
  $(error Aborting)
endif

# sanity check -- libxslt
ifeq ($(XSLT_VER),)
  $(warning *** Could not find  libxslt.)
  $(warning *** Please check that libxslt-dev or similar is installed.)
  $(error Aborting)
endif

include mk/bits.mk

# another sanity check. Note: $(BITS) is set by mk/bits.mk
ifeq ($(DISABLE_Yices),)
  ifneq ($(shell test -f src/logic/src/yices/$(BITS)bit/lib/libyices.a || echo NO),)
    $(warning *** src/logic/src/yices/$(BITS)bit/lib/libyices.a does not exist.)
    $(warning *** Please refer to the README file for instructions on fetching)
    $(warning *** Yices.)
    $(warning *** You can build without Yices using   make DISABLE_Yices=1)
    $(error Aborting)
  endif
endif

# tools
TOOLS=cat csi ttt2

# list of packages to consider
TOPLEVEL  := Automata Experiments Logic Parsec Processors Rewriting Ttt2 Util Hello

# flags for linking
STDLIBS   := nums str unix
LINK      := $(if $(STATIC),-ccopt -static,) -cc g++ $(STDLIBS:=.cmxa)

# default target. (see src/ttt2/build.mk)
all: ttt2

.SUFFIXES:

include mk/toplevel.mk

# helpers for building file names
make-xcmi = $(BUILD_$(1))/$(call lower,$(1))x.cmi
make-mli = $(SRC_$(1))/$(call lower,$(1)).mli
make-inc = -I $(DIR_$(1))

# make an ocaml toplevel interpreter that includes the Ttt2 packages
top: top.build/top $(DIR)/build.mk
	cp $(LIBS_Ttt2:.cmxa=.cmi) $(call map,make-xcmi,$(PACKS_Ttt2)) top.build
	@( echo '#! /bin/bash' ; \
	   echo 'exec $(shell pwd)/top.build/top -I $(shell pwd)/top.build "$$@"' ) > top
	chmod +x top

top.build/top: $$(subst .cmxa,.cma,$$(LIBS_Ttt2)) $(EXTRA_Ttt2) | top.build/.dir
	$(OCAMLTOP) $(LINK:.cmxa=.cma) $(subst .cmx,.cmo,$(LINK_Logic:.cmxa=.cma)) -o $@ $(LIBS_Ttt2:.cmxa=.cma) $(LINK_Ttt2)

# build documentation
doc: $(LIBS_Ttt2) README.txt | doc/.dir
	$(OCAMLDOC) -html -d doc -text README.txt $(call map,make-mli,$(PACKS_Ttt2)) $(call map,make-inc,$(PACKS_Ttt2))

README.txt: README
	cp $< $@

.INTERMEDIATE: README.txt

# extra housekeeping
distclean::
	rm -rf top top.build doc build $(add_suffix .tar.gz,$(TOOLS))

clean::
	rm -f README.txt

# misc
exec: ttt2

help:
	@cat README

.PHONY: exec doc help

# wrappers and packaging
cat csi: %: %-runme %-starexec

%_runme: %-runme %-starexec
$(addsuffix -runme,$(TOOLS)): %-runme: ttt2 | build/%/.dir
	mk/tool-runme $(subst -runme,,$@)
$(addsuffix -starexec,$(TOOLS)): %-starexec: ttt2 | build/%/.dir
	mk/tool-starexec $(subst -starexec,,$@)

%_online: %-online
ifndef DISABLE_Yices
$(addsuffix -online,$(TOOLS)): %-online:
	@echo "*** Please rebuild TTT2 without Yices:"
	@echo "make clean-logic"
	@echo "make DISABLE_Yices=1 $@"
	@echo "make clean-logic   # to get back to normal"
else
$(addsuffix -online,$(TOOLS)): %-online: %-dir
	mk/tool-online $(subst -online,,$@)
endif

$(addsuffix -dir,$(TOOLS)): %-dir: %-runme
	mk/tool-dir $(subst -dir,,$@)
ifndef DISABLE_Yices
	@echo "***************************************************"
	@echo "*** Warning: This build seems to include Yices. ***"
	@echo "***************************************************"
endif

.PHONY: %-runme %-dir %-online %_runme %_online

