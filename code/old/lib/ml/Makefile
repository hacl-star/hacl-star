include ../../../Makefile.include

FSTAR_LIB_ML=$(FSTAR_LIB)/ml

FILES= \
	Hacl_UInt8.mli Hacl_UInt8.ml \
	Hacl_UInt32.mli Hacl_UInt32.ml \
	Hacl_UInt64.mli Hacl_UInt64.ml \
	Hacl_UInt128.mli Hacl_UInt128.ml \
	Hacl_Cast.ml

OBJS=$(FILES:.ml=.o)
CMX=$(FILES:.ml=.cmx)

all: hacllib.cmxa

hacllib.cmxa:
	$(OCAMLOPT) -thread -w -58 -c $(FILES)
	$(OCAMLOPT_BARE) -package fstarlib -a $(CMX) -o hacllib.cmxa

clean:
	rm -f *.cmi *.cmo *.cmx *.cmxa *.o *.a *~
