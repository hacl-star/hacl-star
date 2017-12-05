include ../../Makefile.include

FSTAR_ARGS=$(OTHERFLAGS)

# OCaml variables
OCAMLOPT := $(OCAMLOPT) -w -8-20-26-28-10
FSTAR_INCLUDES+=--include $(HACL_HOME)/specs/lib --include $(HACL_HOME)/specs/lemmas

all:
	$(MAKE) lib
	$(MAKE) sha2.exe chacha20-vec.exe chacha20-vec2.exe chacha20-vec256.exe secretbox.exe rsa.exe

EXTRACTED= FStar_Seq_Base.ml FStar_Seq.ml FStar_Seq_Properties.ml FStar_Math_Lib.ml FStar_BitVector.ml FStar_UInt.ml  FStar_Endianness.ml

NOEXTRACT=$(addprefix --no_extract FStar., Classical Ghost Int16 Int32 Int64 Int63 Int16 Int8 Int.Cast Int List.Tot.Base List.Tot List.Tot.Properties Math.Lemmas Mul StrongExcludedMiddle UInt128 UInt16 UInt32 UInt63 UInt64 UInt8) $(addprefix --no_extract Hacl., UInt64 UInt32 UInt8)

ARGS=--codegen OCaml --lax --include $(HACL_HOME)/code/lib/kremlin $(NOEXTRACT) --include $(KREMLIN_HOME)/kremlib --include ..

OCAML_INCLUDES=-I $(HACL_HOME)/code/lib/ml $(HACL_HOME)/code/lib/ml/hacllib.cmxa 

%.fst-verify: %.fst
	$(FSTAR) --include $(HACL_HOME)/code/lib/kremlin --include $(KREMLIN_HOME)/kremlib --include .. --use_hints $*.fst

lib:
	$(MAKE) -C $(HACL_HOME)/code/lib/ml MEM=HST

secretbox.exe: Spec.HSalsa20.fst Spec.SecretBox.fst
	$(MAKE) -C ../code/lib/ml MEM=HST
	mkdir -p secretbox-spec
	$(FSTAR) $(ARGS) --odir secretbox-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else failwith "Test failed\n")' >> secretbox-spec/Spec_SecretBox.ml
	$(OCAMLOPT) -I secretbox-spec $(OCAML_INCLUDES) $(addprefix secretbox-spec/, $(EXTRACTED)) secretbox-spec/Spec_Loops.ml secretbox-spec/Spec_Lib.ml secretbox-spec/Spec_CTR.ml secretbox-spec/Spec_Salsa20.ml secretbox-spec/Spec_HSalsa20.ml secretbox-spec/Spec_Poly1305_Lemmas.ml secretbox-spec/Spec_Poly1305.ml secretbox-spec/Spec_SecretBox.ml -o secretbox.exe
	./secretbox.exe

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

sha2_256.exe: Spec.SHA256.fst
	$(MAKE) lib
	mkdir -p sha2-spec
	$(FSTAR) $(ARGS) --odir sha2-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> sha2-spec/Spec_SHA256.ml
	$(OCAMLOPT) -I sha2-spec $(OCAML_INCLUDES) $(addprefix sha2-spec/, $(EXTRACTED)) sha2-spec/Spec_Loops.ml sha2-spec/Spec_Lib.ml sha2-spec/Seq_Create.ml sha2-spec/Spec_SHA256.ml -o sha2_256.exe
	./sha2_256.exe

rsa.exe: ../lib/fst/Spec.Lib.IntTypes.fst ../lib/fst/Spec.Lib.RawIntTypes.fst ../lib/fst/Spec.Lib.IntSeq.fst ../lib/fst/Spec.Lib.Stateful.fst ../Spec.SHA2.fst Spec.RSA.fst Spec.RSA.Test.fst
	$(MAKE) -C ../../code/lib/ml
	mkdir -p rsa-spec
	$(FSTAR) --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes  --extract_module Spec.Lib.IntSeq --extract_module Spec.Lib.Stateful --extract_module Spec.SHA2 --extract_module Spec.RSA --extract_module Spec.RSA.Test --extract_module Spec.RSA.Test --odir rsa-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else failwith "Test failed\n")' >> rsa-spec/Spec_RSA_Test.ml
	$(OCAMLOPT) -I rsa-spec $(OCAML_INCLUDES) rsa-spec/Spec_Lib_IntTypes.ml rsa-spec/Spec_Lib_RawIntTypes.ml rsa-spec/Spec_Lib_IntSeq.ml rsa-spec/Spec_Lib_Stateful.ml rsa-spec/Spec_SHA2.ml rsa-spec/Spec_RSA.ml rsa-spec/Spec_RSA_Test.ml -o rsa.exe
	./rsa.exe
	
clean:
	$(MAKE) -C $(HACL_HOME)/code/lib/ml clean
	rm -rf *.cmi *.cmo *.cmx *.o *~ *.out *.exe chacha-spec-vec3 chacha-spec-vec256 chacha-spec-vec2 chacha-spec-vec sha2-spec ed25519-spec secretbox-spec rsa-spec