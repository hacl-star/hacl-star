include ../../Makefile.include

FSTAR_LIB_ML=$(FSTAR_LIB)/ml
FILES=Hacl_UInt32.mli Hacl_UInt32.ml Hacl_UInt64.mli Hacl_UInt64.ml Hacl_UInt8.mli Hacl_UInt8.ml Hacl_UInt128.mli Hacl_UInt128.ml Hacl_Cast.ml
FILESX=Hacl_UInt32.cmx Hacl_UInt64.cmx Hacl_UInt8.cmx  Hacl_UInt128.cmx Hacl_Cast.cmx

OBJS=$(FILES:.ml=.o)
CMX=$(FILES:.ml=.cmx)

all: hacllib.cmxa

include ../Makefile.include

hacllib.cmxa:
	FSTAR_HOME=$(abspath $(FSTAR_HOME)) $(MAKE) -C $(FSTAR_LIB_ML)
	$(OCAMLOPT) -thread -w -58 -c $(FILES)
	$(OCAMLOPT_BARE) -a $(FILESX) -o hacllib.cmxa

clean:
	FSTAR_HOME=$(abspath $(FSTAR_HOME)) $(MAKE) -C $(FSTAR_LIB_ML) clean
	rm -f *.cmi *.cmo *.cmx *.cmxa *.o *.a *~
