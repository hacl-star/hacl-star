include ../Makefile.include

HACL_API=$(HACL_HOME)/crypto
HACL_CRYPTO_UTILS=$(HACL_API)/utils
HACL_SYMMETRIC=$(HACL_API)/symmetric
HACL_HASH=$(HACL_API)/hash
HACL_EC=$(HACL_API)/ec

KREMLIN_ARGS+=$(VERBOSE) \
	-ccopt -Wno-error=pointer-sign \
	-ccopt -Wno-error=incompatible-pointer-types \
	-ccopt -Wno-error=format=

KREMLIN_ARGS+=-fsopt "--use_hints" -skip-extraction -verify $(VERBOSE) -skip-compilation

OCAMLOPT:=$(OCAMLOPT) -thread -package batteries,zarith,stdint -w -20-26-3-8-58
OCAML_OPTIONS=-fsopt "--lax" -fsopt "--codegen OCaml" -fsopt "--no_location_info"


ALL=Hacl.UInt8.fst Hacl.UInt16.fst Hacl.UInt32.fst Hacl.UInt64.fst Hacl.UInt128.fst Hacl.Cast.fst

all: $(addsuffix -verify, $(ALL))

ML=$(addprefix ml/, $(ALL:.fst=.ml))
OBJS=$(FILES:.ml=.o)
CMX=$(FILES:.ml=.cmx)
OCAMLOPT=$(OCAMLOPT) $(INCLUDES)

.SUFFIXES: .ml .mli .cmo .cmi .cmx

%.o: %.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c -I ml $<

ml: $(ML) $(CMX) $(OBJS)

clean:
	rm -f *~ $(addprefix ml/, *.cmo *.cmi *.o *~ *.cmx)
