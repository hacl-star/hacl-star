FSTAR_HOME?=../../../dependencies/FStar
HYPERSTACK=$(FSTAR_HOME)/ulib/hyperstack
FSTAR=$(FSTAR_HOME)/bin/fstar.exe --include $(HYPERSTACK)

OPTIONS_VER=

ALL=Hacl.SBuffer.fst Hacl.UInt8.fst Hacl.UInt16.fst Hacl.UInt32.fst Hacl.UInt64.fst Hacl.UInt128.fst Hacl.Cast.fst

all: $(addsuffix -ver, $(ALL))

%-ver: %
	$(FSTAR) $^


FILES=$(addprefix ml/,Hacl_UInt8.mli Hacl_UInt8.ml Hacl_UInt16.mli Hacl_UInt16.ml Hacl_UInt32.ml Hacl_UInt64.ml Hacl_UInt128.ml Hacl_Cast.ml Hacl_Utils.ml Hacl_SBuffer.ml)

OBJS=$(FILES:.ml=.o)
CMX=$(FILES:.ml=.cmx)
OCAMLOPT=ocamlfind opt -thread -package batteries,zarith,stdint -linkpkg -g $(INCLUDES)
OCAMLDEP=ocamlfind dep
OCAMLMKLIB=ocamlfind mklib
.SUFFIXES: .ml .mli .cmo .cmi .cmx

%.o: %.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c -I ml -I $(FSTAR_HOME)/ulib/ml -linkpkg $<


ml: $(CMX) $(OBJS)

clean:
	rm -f *~ $(addprefix ml/, *.cmo *.cmi *.o *~ *.cmx)
