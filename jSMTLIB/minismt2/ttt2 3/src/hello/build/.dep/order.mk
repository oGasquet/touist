all: src/hello/build/main.cmx ;
include main.ml
src/hello/%.cmx: ; @echo $@
%: ;
