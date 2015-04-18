# $Id: Makefile,v 1.44 2013/10/28 07:45:30 hzankl Exp $

# Copyright 2009 Harald Zankl
# GNU Lesser General Public License
#
# This file is part of MiniSmt.
# 
# MiniSmt is free software: you can redistribute it and/or modify it under
# the terms of the GNU Lesser General Public License as published by the
# Free Software Foundation, either version 3 of the License, or (at your
# option) any later version.
# 
# MiniSmt is distributed in the hope that it will be useful, but WITHOUT ANY
# WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public
# License for more details.
# 
# You should have received a copy of the GNU Lesser General Public
# License along with MiniSmt. If not, see <http://www.gnu.org/licenses/>.

#TTT2=/home/sarah/swinkler/tools/fightinghydra/ghm
TTT2=/Users/blida/Documents/M1-UPS/Semestre2/PROJET/touist1/jSMTLIB/minismt2/ttt2
ifeq ($(TTT2HOME),)
TTT2DEFAULT=../ttt2
$(warning *** TTT2HOME variable not set, using $(TTT2DEFAULT).)
TTT2=$(TTT2DEFAULT)
endif
DISABLE_Yices=1

STATIC = -ccopt -static
LINK = $(if $(STATIC),-ccopt -static,)
BASEDIRS = 
DIRS = $(addprefix src/, $(BASEDIRS)) 
INCLUD = util parsec logic
GPW=gpw
INCLUDE = $(addprefix -I $(TTT2)/src/, $(INCLUD)) \
          -I src -I src/yices -I src/dummy \
          $(addprefix -I $(TTT2)/src/logic/build-lib/, yices minisat+ minisat picosat $(GPW)) \
	  -ccopt -L$(TTT2)/src/logic/src/yices/32bit/lib \
	  -ccopt -L$(TTT2)/src/logic/src/yices/64bit/lib

ifeq ($(DISABLE_Yices),) 
 YICES_LIBS = yices yices2
endif

LIBS = nums str unix util minisat minisatp $(GPW) $(YICES_LIBS) picosat $(INCLUD)
LIBS_CMA = $(addsuffix .cma, $(LIBS))
LIBS_CMXA = $(addsuffix .cmxa, $(LIBS))
FLAGS = -cc g++ -g
OCAMLC = ocamlc -g $(INCLUDE) $(FLAGS)
OCAMLOPT = ocamlopt -g $(INCLUDE) $(FLAGS)
MKTOP = ocamlmktop $(INCLUDE) $(FLAGS)

ML_PRE_PARSE=\
 debug.ml \
 smtFormula.ml \
 ops.ml \

bitvector= bitvector.ml
BV=bv
ifneq ($(DISABLE_Yices),) 
 BV=  
 bitvector= dummy/bitvector.ml
endif

ML_FILES= \
 $(ML_PRE_PARSE) \
 parser.ml \
 lexer.ml \
 parser2.ml \
 lexer2.ml \
 bvparser.ml \
 bvlexer.ml \
 bv.ml \
 bvNat.ml \
 bvInt.ml \
 bvRat.ml \
 bvReal.ml \
 bvReal2.ml \
 $(bitvector) \
 pb2cnf.ml \
 pb2bdd.ml \
 smt2pbc.ml \
 main.ml \
 
ML_NAMES=$(addprefix src/, $(basename $(ML_FILES)))
ML_PRE=$(addprefix src/, $(ML_PRE_PARSE))
CMO_FILES=$(addsuffix .cmo, $(ML_NAMES))
CMX_FILES=$(addsuffix .cmx, $(ML_NAMES))
TARGET=minismt
VERSION=`cat .version`
ONLINE=minismt-$(VERSION).tar.gz
OPATH=colo1-c703.uibk.ac.at:/home/www/colo1-c703/software/minismt
CLIBS=-cclib -lgmp

all: ttt2 Makefile $(BV) parse bytecode native

bytecode: $(CMO_FILES)

bv:
	cd src/yices; $(MAKE); 

comp: #dist_clean all
	echo "please use special competition version"
	#echo '#!/bin/sh' > run
	#echo './minismt -comp $$*' >> run
	#chmod +x run
	#zip comp.zip run minismt

native: $(CMX_FILES)
	$(OCAMLOPT) $(LINK) -o $(TARGET) $(LIBS_CMXA) $(CMX_FILES) $(CLIBS)

new: 
	$(MAKE) dist_clean
	$(MAKE)

online:
	$(MAKE) all
	@if [[ $(VERSION) == `./$(TARGET) -v` ]]; then \
	 echo "There already exists a version `cat .version`"; exit 1; fi;
	./$(TARGET) -v > .version
	$(MAKE) dist_clean
	mkdir minismt
	cp -r src LICENCE README Makefile test.smt minismt
	tar cfz $(ONLINE) minismt
	scp $(ONLINE) $(OPATH)/download/
	scp .version $(OPATH)
	scp .changelog $(OPATH)
	rm -rf $(ONLINE)
	rm -rf minismt

parse:
	$(OCAMLC) -c $(ML_PRE)
	$(OCAMLOPT) -c $(ML_PRE)
	ocamllex src/lexer.mll
	ocamllex src/bvlexer.mll
	ocamlyacc src/parser.mly
	ocamlyacc src/bvparser.mly
	$(OCAMLC)  src/parser.mli 
	$(OCAMLC)  src/bvparser.mli 
	ocamllex src/lexer2.mll
	ocamlyacc src/parser2.mly
	$(OCAMLC)  src/parser2.mli 
ttt2: 
	cd $(TTT2); $(MAKE) native-logic DISABLE_Yices=$(DISABLE_Yices) ;

ttt2_clean: 
	cd $(TTT2); $(MAKE) distclean;

clean:
	cd src/yices; $(MAKE) clean;
	rm -rf src/{lexer,parser,bvlexer,bvparser,lexer2,parser2}.{ml,mli,cmi,cmo,cmx}
	rm -rf src/*.{o,cmo,cmi,cmx} src/dummy/*.{o,cmo,cmi,cmx}
	rm -rf comp.zip run

clear:

dist_clean: clean
	rm -rf $(TARGET)
	rm -rf minismt

help:
	@cat README

top: Makefile all
	$(MKTOP) -o all.top $(LIBS_CMA)

%.cmi: %.mli
	$(OCAMLC) -c $<

%.cmo: %.ml
	$(OCAMLC) -c $<

%.cmx: %.ml
	$(OCAMLOPT) -c $<

.PHONY: all clean clear dist_clean doc top
