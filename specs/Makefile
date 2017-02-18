FSTAR_HOME?=../../../dependencies/FStar
HACL_HOME?=../..

include $(FSTAR_HOME)/src/gmake/fstar.mk
include $(FSTAR_HOME)/ulib/ml/Makefile.include

FSTAR_ARGS=$(OTHERFLAGS)

# OCaml variables
OCAMLOPT := $(OCAMLOPT) -w -8-20-26-28-10

all: poly1305.exe chacha20.exe salsa20.exe secretbox.exe

EXTRACTED= FStar_Seq_Base.ml FStar_Seq.ml FStar_Seq_Properties.ml FStar_Math_Lib.ml FStar_BitVector.ml FStar_UInt.ml  FStar_Endianness.ml 

NOEXTRACT=$(addprefix --no_extract FStar., Classical Ghost Int16 Int32 Int64 Int63 Int16 Int8 Int.Cast Int List.Tot.Base List.Tot List.Tot.Properties Math.Lemmas Mul StrongExcludedMiddle UInt128 UInt16 UInt32 UInt63 UInt64 UInt8) $(addprefix --no_extract Hacl., UInt64 UInt32 UInt8)

ARGS=--codegen OCaml --lax --include ../code/lib/kremlin $(NOEXTRACT)

poly1305.exe: Spec.Poly1305.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p poly-spec
	$(FSTAR) $(ARGS) --odir poly-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> poly-spec/Spec_Poly1305.ml
	$(OCAMLOPT) -I poly-spec -I ../code/lib/ml ../code/lib/ml/hacllib.cmxa $(addprefix poly-spec/, $(EXTRACTED)) poly-spec/Spec_Poly1305.ml -o poly1305.exe
	./poly1305.exe

chacha20.exe: Spec.Lib.fst Spec.CTR.fst Spec.Chacha20.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p chacha-spec
	$(FSTAR) $(ARGS) --odir chacha-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> chacha-spec/Spec_Chacha20.ml
	$(OCAMLOPT) -I chacha-spec -I ../code/lib/ml ../code/lib/ml/hacllib.cmxa $(addprefix chacha-spec/, $(EXTRACTED)) chacha-spec/Spec_Lib.ml chacha-spec/Spec_CTR.ml chacha-spec/Spec_Chacha20.ml -o chacha20.exe
	./chacha20.exe

salsa20.exe: Spec.Lib.fst Spec.CTR.fst Spec.Salsa20.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p salsa-spec
	$(FSTAR) $(ARGS) --odir salsa-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> salsa-spec/Spec_Salsa20.ml
	$(OCAMLOPT) -I salsa-spec -I ../code/lib/ml ../code/lib/ml/hacllib.cmxa $(addprefix salsa-spec/, $(EXTRACTED)) salsa-spec/Spec_Lib.ml salsa-spec/Spec_CTR.ml salsa-spec/Spec_Salsa20.ml -o salsa20.exe
	./salsa20.exe

secretbox.exe: Spec.Lib.fst Spec.CTR.fst Spec.Salsa20.fst Spec.HSalsa20.fst Spec.Poly1305.fst Spec.SecretBox.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p secretbox-spec
	$(FSTAR) $(ARGS) --odir secretbox-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> secretbox-spec/Spec_SecretBox.ml
	$(OCAMLOPT) -I secretbox-spec -I ../code/lib/ml ../code/lib/ml/hacllib.cmxa $(addprefix secretbox-spec/, $(EXTRACTED)) secretbox-spec/Spec_Lib.ml secretbox-spec/Spec_CTR.ml secretbox-spec/Spec_Salsa20.ml secretbox-spec/Spec_HSalsa20.ml secretbox-spec/Spec_Poly1305.ml secretbox-spec/Spec_SecretBox.ml -o secretbox.exe
	./secretbox.exe


clean:
	$(MAKE) -C ../code/lib/ml clean
	rm -rf *.cmi *.cmo *.cmx *.o *~ *.out *.exe poly-spec
