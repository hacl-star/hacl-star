include ../Makefile.include
include Makefile.include

ALL=Hacl.SBuffer.fst Hacl.UInt8.fst Hacl.UInt16.fst Hacl.UInt32.fst Hacl.UInt64.fst Hacl.UInt128.fst Hacl.Cast.fst

all: $(addsuffix -ver, $(ALL))

FILES=$(addprefix ml/,Hacl_UInt8.mli Hacl_UInt8.ml Hacl_UInt16.mli Hacl_UInt16.ml Hacl_UInt32.ml Hacl_UInt64.ml Hacl_UInt128.ml Hacl_Cast.ml Hacl_Utils.ml Hacl_SBuffer.ml)

OBJS=$(FILES:.ml=.o)
CMX=$(FILES:.ml=.cmx)
OCAMLOPT=$(OCAMLOPT) $(INCLUDES)

.SUFFIXES: .ml .mli .cmo .cmi .cmx

%.o: %.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c -I ml $<

ml: $(CMX) $(OBJS)

clean:
	rm -f *~ $(addprefix ml/, *.cmo *.cmi *.o *~ *.cmx)
