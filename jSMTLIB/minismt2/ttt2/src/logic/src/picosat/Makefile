# Copyright 2008 Martin Korp, Christian Sternagel, Harald Zankl
# GNU Lesser General Public License
#
# This file is part of TTT2.
# 
# TTT2 is free software: you can redistribute it and/or modify it under
# the terms of the GNU Lesser General Public License as published by the
# Free Software Foundation, either version 3 of the License, or (at your
# option) any later version.
# 
# TTT2 is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public
# License for more details.
# 
# You should have received a copy of the GNU Lesser General Public
# License along with TTT2. If not, see <http://www.gnu.org/licenses/>.

SHELL = bash
CAML = $(shell ocamlc -where)
OCAMLC = ocamlc -cc g++
OCAMLOPT = ocamlopt -cc g++
PSAT = picosat
PINCLUDE = -I picosat

COBJS = \
 picosatInterface_stubs.o \

FILES = \
 picosatInterface

CMI = $(addsuffix .cmi, $(FILES))
CMO = $(addsuffix .cmo, $(FILES))
CMX = $(addsuffix .cmx, $(FILES))
CLIBS = interface_picosat picosat camlidl
CLIBFLAGS = $(addprefix -cclib -l, $(CLIBS))
CFLAGS = -fPIC -DPIC -Wall -I $(CAML) $(PINCLUDE)
CXX = g++ $(CFLAGS) 

all:
	pushd $(PSAT); ./configure; $(MAKE); popd
	camlidl -header picosatInterface.idl
	$(MAKE) picosatInterface_stubs.o $(CMI) $(CMO)
	ar rcs libinterface_picosat.a $(COBJS)
	$(OCAMLC) -custom -a -o picosat.cma $(CLIBFLAGS) $(CMO)
	$(MAKE) $(CMX)
	$(OCAMLOPT) -a -o picosat.cmxa $(CLIBFLAGS) $(CMX)
	@cp $(PSAT)/libpicosat.a .

clean:
	rm -f *.o *.h *.cmi *.cmo 
	rm -f picosatInterface{.ml,.mli,_stubs.c} libinterface_picosat.a
	rm -f test

dist_clean: clean
	pushd $(PSAT); $(MAKE) clean; popd
	rm -f *.cma *.cmx *.cmxa *.a test_native


# build rules
%.o: %.c
	ocamlc -cc cc -ccopt "-fPIC -DPIC -Wall" -c $<

%.x: %.C
	g++ $(CFLAGS) -c $<

%.cmi: %.mli
	$(OCAMLC) -c $<
        
%.cmo: %.ml
	$(OCAMLC) -c $<
        
%.cmx: %.ml
	$(OCAMLOPT) -c $<

.PHONY: all test
