FSTAR_HOME?=../../../dependencies/FStar

FILES=Hacl_UInt32.mli Hacl_UInt32.ml Hacl_UInt64.mli Hacl_UInt64.ml Hacl_UInt8.mli Hacl_UInt8.ml  Hacl_UInt128.mli Hacl_UInt128.ml Hacl_Cast.ml
FILESX=Hacl_UInt32.cmx Hacl_UInt64.cmx Hacl_UInt8.cmx  Hacl_UInt128.cmx Hacl_Cast.cmx

OBJS=$(FILES:.ml=.o)
CMX=$(FILES:.ml=.cmx)

all: hacllib.cmxa

include ../Makefile.include

hacllib.cmxa:
<<<<<<< HEAD
	$(MAKE) -C $(ULIB_ML)
	$(OCAMLOPT) -c $(FILES)
	OCAMLPATH="$(FSTAR_HOME)/bin" ocamlfind opt -a -package fstarlib $(FILESX) -o hacllib.cmxa
=======
	$(MAKE) -C $(FSTAR_LIB)
	$(OCAMLOPT) -thread -w -58 -c $(FILES)
	$(OCAMLOPT) -a $(FILESX) -o hacllib.cmxa
>>>>>>> migrating_sts

clean:
	$(MAKE) -C $(ULIB_ML) clean
	rm -f *.cmi *.cmo *.cmx *.cmxa *.o *.a *~
