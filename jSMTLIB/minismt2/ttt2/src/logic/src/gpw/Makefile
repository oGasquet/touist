#/**************************************************************************************************
#
#accessGpw.c - modified Main.C from (C) Niklas Een, Niklas Sörensson, 2004
#
#**************************************************************************************************/

CAML=$(shell ocamlc -where)
# Sources, Headers ans Objects for GPW/Minisat+
CSRCS = $(wildcard gpw/*.C)
CHDRS = $(wildcard gpw/*.h) accessGpw.h
COBJS = $(addsuffix .o, $(basename $(CSRCS)))\
 gpw/ADTs/Global.o\
 gpw/ADTs/FEnv.o\
 gpw/ADTs/File.o\
 accessGpw_stubs.o\
 accessGpw.o

# Compilers and directory for caml headers
CXX = g++
CC = cc

# flags to compile minisat+
CFLAGS = -Wall -ffloat-store 
CFLAGS += \
 -Igpw \
 -Igpw/ADTs \
 -include Global.h \
 -include accessGpw.h \
 -D_FILE_OFFSET_BITS=64
CFLAGS   += -I/usr/local/include -fno-strict-aliasing

COPTIMIZE = -O3 #-fomit-frame-pointer # -falign-loops=4 -falign-functions=16 -foptimize-sibling-calls -finline-functions -fcse-follow-jumps -fcse-skip-blocks -frerun-cse-after-loop -frerun-loop-opt -fgcse

LDFLAGS  += -L/usr/local/lib

CFLAGS += $(COPTIMIZE) -D NDEBUG #-D NO_GMP #usual rx minisat+
OBJS =  gpwSolver.cmo
OBJX =  gpwSolver.cmx

.PHONY : all clean depend

FLAGS= -cc g++ -cclib -lcamlidl -cclib -lgpw
INCLUDE = -I ../../../ttt2/src/util
OCAMLC=ocamlc $(FLAGS) $(INCLUDE) 
OCAMLOPT=ocamlopt $(FLAGS) $(INCLUDE)

TARGET=gpw

libgpw.a : $(COBJS) $(OBJS) $(OBJX)
	ar rc libgpw.a $(COBJS)
	ranlib libgpw.a
	$(OCAMLC) -a -o $(TARGET).cma -custom $(OBJS) -cclib -lgpw
	$(OCAMLOPT) -a -o $(TARGET).cmxa $(OBJX) -cclib -lgpw

build:
	@echo Building $(EXEC) "("$(WAY)")"

clean:
	@rm -f $(COBJS) depend.mak libgpw.a
	@rm -f *.mli *.cmi *.cmo *.cmx
	@rm -f accessGpw{_stubs.c,.h}


## Build rules
%.cmo : %.ml 
	$(OCAMLC) -c $<

%.cmx : %.ml 
	$(OCAMLOPT) -c $<

accessGpw_stubs.o: accessGpw_stubs.c
	$(CC) -c -Wall $(LDFLAGS) -I $(CAML) -I. accessGpw_stubs.c

%.o : %.C
	@echo Compiling: $<
	@$(CXX) $(CFLAGS) $(LDFLAGS) -I. -c -o $@ $<


## Make dependencies
depend:	depend.mak

depend.mak:	 $(CHDRS) $(CSRCS)
	@echo Making dependencies...
	@$(CXX) -MM $(CSRCS) $(CFLAGS) $(LDFLAGS) > depend.mak
	@cp depend.mak /tmp/depend.mak.tmp
	@sed "s/o:/op:/" /tmp/depend.mak.tmp >> depend.mak
	@sed "s/o:/od:/" /tmp/depend.mak.tmp >> depend.mak
	@sed "s/o:/or:/" /tmp/depend.mak.tmp >> depend.mak
	@sed "s/o:/ox:/" /tmp/depend.mak.tmp >> depend.mak
	@rm /tmp/depend.mak.tmp

include depend.mak
