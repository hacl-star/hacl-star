FSTAR_HOME?=../../../dependencies/FStar
HACL_HOME?=../..

include $(FSTAR_HOME)/src/gmake/fstar.mk
include $(FSTAR_HOME)/ulib/ml/Makefile.include

FSTAR_ARGS=$(OTHERFLAGS)

# OCaml variables
OCAMLOPT := $(OCAMLOPT) -w -8-20-26-28-10

all: poly

EXTRACTED= FStar_Seq_Base.ml FStar_Seq.ml FStar_Seq_Properties.ml FStar_Math_Lib.ml FStar_BitVector.ml FStar_UInt.ml  FStar_Endianness.ml 

poly:
	$(MAKE) -C ../code/lib/ml
	mkdir -p poly-spec
	$(FSTAR) --codegen OCaml Spec.Poly1305.fst --odir poly-spec --include ../code/lib/kremlin
	echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> poly-spec/Spec_Poly1305.ml
	$(OCAMLOPT) -I poly-spec -I ../code/lib/ml ../code/lib/ml/hacllib.cmxa $(addprefix poly-spec/, $(EXTRACTED)) poly-spec/Spec_Poly1305.ml
	./a.out

clean:
	rm -rf *.cmi *.cmo *.cmx *.o *~ *.out poly-spec
