FSTAR_HOME?=../../dependencies/FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
HACL_HOME?=../..

include $(FSTAR_HOME)/src/gmake/fstar.mk
include $(FSTAR_HOME)/ulib/ml/Makefile.include

FSTAR_ARGS=$(OTHERFLAGS)

# OCaml variables
OCAMLOPT := $(OCAMLOPT) -w -8-20-26-28-10

all:
	$(MAKE) lib
	$(MAKE) sha2.exe chacha20-vec.exe chacha20-vec2.exe chacha20-vec256.exe

EXTRACTED= FStar_Seq_Base.ml FStar_Seq.ml FStar_Seq_Properties.ml FStar_Math_Lib.ml FStar_BitVector.ml FStar_UInt.ml  FStar_Endianness.ml

NOEXTRACT=$(addprefix --no_extract FStar., Classical Ghost Int16 Int32 Int64 Int63 Int16 Int8 Int.Cast Int List.Tot.Base List.Tot List.Tot.Properties Math.Lemmas Mul StrongExcludedMiddle UInt128 UInt16 UInt32 UInt63 UInt64 UInt8) $(addprefix --no_extract Hacl., UInt64 UInt32 UInt8)

ARGS=--codegen OCaml --lax --include $(HACL_HOME)/code/lib/kremlin $(NOEXTRACT) --include $(KREMLIN_HOME)/kremlib --include ..

OCAML_INCLUDES=-I $(HACL_HOME)/code/lib/ml $(HACL_HOME)/code/lib/ml/hacllib.cmxa 

%.fst-ver: %.fst
	$(FSTAR) --include $(HACL_HOME)/code/lib/kremlin --include $(KREMLIN_HOME)/kremlib --include .. --use_hints $*.fst

lib:
	$(MAKE) -C $(HACL_HOME)/code/lib/ml MEM=HST

sha2.exe: Spec.SHA2.fst
	$(MAKE) lib
	mkdir -p sha2-spec
	$(FSTAR) $(ARGS) --odir sha2-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> sha2-spec/Spec_SHA2.ml
	$(OCAMLOPT) -I sha2-spec $(OCAML_INCLUDES) $(addprefix sha2-spec/, $(EXTRACTED)) sha2-spec/Spec_Loops.ml sha2-spec/Spec_Lib.ml sha2-spec/Seq_Create.ml sha2-spec/Spec_SHA2.ml -o sha2.exe
	./sha2.exe

chacha20-vec.exe: Spec.Chacha20_vec.fst
	$(MAKE) lib
	mkdir -p chacha-spec-vec
	$(FSTAR) $(ARGS) --odir chacha-spec-vec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> chacha-spec-vec/Spec_Chacha20_vec.ml
	$(OCAMLOPT) -I chacha-spec-vec $(OCAML_INCLUDES) $(addprefix chacha-spec-vec/, $(EXTRACTED)) chacha-spec-vec/Spec_Loops.ml chacha-spec-vec/Spec_Lib.ml chacha-spec-vec/Spec_CTR.ml chacha-spec-vec/Spec_Chacha20_vec.ml -o chacha20-vec.exe
	./chacha20-vec.exe

chacha20-vec2.exe: Spec.Chacha20_vec2.fst
	$(MAKE) lib
	mkdir -p chacha-spec-vec2
	$(FSTAR) $(ARGS) --odir chacha-spec-vec2 $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> chacha-spec-vec2/Spec_Chacha20_vec2.ml
	$(OCAMLOPT) -I chacha-spec-vec2 $(OCAML_INCLUDES) $(addprefix chacha-spec-vec2/, $(EXTRACTED)) chacha-spec-vec2/Spec_Loops.ml chacha-spec-vec2/Spec_Lib.ml chacha-spec-vec2/Spec_CTR.ml chacha-spec-vec2/Spec_Chacha20_vec2.ml -o chacha20-vec2.exe
	./chacha20-vec2.exe

chacha20-vec256.exe: Spec.Chacha20_vec256.fst
	$(MAKE) lib
	mkdir -p chacha-spec-vec256
	$(FSTAR) $(ARGS) --odir chacha-spec-vec256 $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> chacha-spec-vec256/Spec_Chacha20_vec256.ml
	$(OCAMLOPT) -I chacha-spec-vec256 $(OCAML_INCLUDES) $(addprefix chacha-spec-vec256/, $(EXTRACTED)) chacha-spec-vec256/Spec_Loops.ml chacha-spec-vec256/Spec_Lib.ml chacha-spec-vec256/Spec_CTR.ml chacha-spec-vec256/Spec_Chacha20_vec256.ml -o chacha20-vec256.exe
	./chacha20-vec256.exe

clean:
	$(MAKE) -C $(HACL_HOME)/code/lib/ml clean
	$(MAKE) -C experimental clean
	rm -rf *.cmi *.cmo *.cmx *.o *~ *.out *.exe chacha-spec-vec3 chacha-spec-vec256 chacha-spec-vec2 chacha-spec-vec sha2-spec
