FSTAR_HOME?=../../../dependencies/FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
HACL_HOME?=../..

include $(FSTAR_HOME)/src/gmake/fstar.mk
include $(FSTAR_HOME)/ulib/ml/Makefile.include

FSTAR_ARGS=$(OTHERFLAGS)

# OCaml variables
OCAMLOPT := $(OCAMLOPT) -w -8-20-26-28-10

all: poly1305.exe chacha20.exe salsa20.exe secretbox.exe chacha20poly1305.exe gf128.exe chacha20-vec.exe chacha20-vec2.exe cryptobox.exe

EXTRACTED= FStar_Seq_Base.ml FStar_Seq.ml FStar_Seq_Properties.ml FStar_Math_Lib.ml FStar_BitVector.ml FStar_UInt.ml  FStar_Endianness.ml

NOEXTRACT=$(addprefix --no_extract FStar., Classical Ghost Int16 Int32 Int64 Int63 Int16 Int8 Int.Cast Int List.Tot.Base List.Tot List.Tot.Properties Math.Lemmas Mul StrongExcludedMiddle UInt128 UInt16 UInt32 UInt63 UInt64 UInt8) $(addprefix --no_extract Hacl., UInt64 UInt32 UInt8)

ARGS=--codegen OCaml --lax --include generic --include ../code/lib/kremlin $(NOEXTRACT) --include $(FSTAR_HOME)/ulib/hyperstack --include $(KREMLIN_HOME)/kremlib

OCAML_INCLUDES=-I ../code/lib/ml -I $(FSTAR_HOME)/ulib/ml/hyperstack ../code/lib/ml/hacllib.cmxa 

%.fst-ver: %.fst
	$(FSTAR) --include generic --include ../code/lib/kremlin --include experimental --include $(FSTAR_HOME)/ulib/hyperstack $*.fst

gf128.exe: Spec.GF128.fst
	$(MAKE) -C ../code/lib/ml MEM=HST
	mkdir -p gf128-spec
	$(FSTAR) $(ARGS) --odir gf128-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else failwith "Test failed\n")' >> gf128-spec/Spec_GF128.ml
	$(OCAMLOPT) -I gf128-spec $(OCAML_INCLUDES) $(addprefix gf128-spec/, $(EXTRACTED)) gf128-spec/Spec_GaloisField.ml gf128-spec/Spec_GF128.ml -o gf128.exe
	./gf128.exe

poly1305.exe: Spec.Poly1305.fst
	$(MAKE) -C ../code/lib/ml MEM=HST
	mkdir -p poly-spec
	$(FSTAR) $(ARGS) --odir poly-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else failwith "Test failed\n")' >> poly-spec/Spec_Poly1305.ml
	$(OCAMLOPT) -I poly-spec $(OCAML_INCLUDES) $(addprefix poly-spec/, $(EXTRACTED)) poly-spec/Spec_Poly1305_Lemmas.ml poly-spec/Spec_Poly1305.ml -o poly1305.exe
	./poly1305.exe

sha2.exe: experimental/Spec.SHA2.fst
	$(MAKE) -C ../code/lib/ml MEM=HST
	mkdir -p sha2-spec
	$(FSTAR) $(ARGS) --odir sha2-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> sha2-spec/Spec_Sha2.ml
	$(OCAMLOPT) -I sha2-spec $(OCAML_INCLUDES) $(addprefix sha2-spec/, $(EXTRACTED)) sha2-spec/Combinators.ml sha2-spec/Spec_Lib.ml sha2-spec/Spec_Sha2.ml -o sha2.exe
	./sha2.exe

curve25519.exe: Spec.Curve25519.fst
	$(MAKE) -C ../code/lib/ml MEM=HST
	mkdir -p curve25519-spec
	$(FSTAR) $(ARGS) --odir curve25519-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else failwith "Test failed\n")' >> curve25519-spec/Spec_Curve25519.ml
	$(OCAMLOPT) -I curve25519-spec $(OCAML_INCLUDES) $(addprefix curve25519-spec/, $(EXTRACTED)) curve25519-spec/C_Loops.ml curve25519-spec/Spec_Lib.ml curve25519-spec/Spec_Curve25519.ml -o curve25519.exe
	./curve25519.exe

chacha20.exe: Spec.Chacha20.fst
	$(MAKE) -C ../code/lib/ml MEM=HST
	mkdir -p chacha-spec
	$(FSTAR) $(ARGS) --odir chacha-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else failwith "Test failed\n")' >> chacha-spec/Spec_Chacha20.ml
	$(OCAMLOPT) -I chacha-spec $(OCAML_INCLUDES) $(addprefix chacha-spec/, $(EXTRACTED)) chacha-spec/C_Loops.ml chacha-spec/Spec_Lib.ml chacha-spec/Spec_CTR.ml chacha-spec/Spec_Chacha20.ml -o chacha20.exe
	./chacha20.exe

chacha20-ml: 
	$(OCAMLOPT) -I chacha-spec $(OCAML_INCLUDES) $(addprefix chacha-spec/, $(EXTRACTED)) chacha-spec/Combinators.ml chacha-spec/Spec_Lib.ml chacha-spec/Spec_CTR.ml chacha-spec/Spec_Chacha20.ml -o chacha20.exe
	./chacha20.exe

chacha20-vec.exe: Spec.Chacha20_vec.fst
	$(MAKE) -C ../code/lib/ml MEM=HST
	mkdir -p chacha-spec-vec
	$(FSTAR) $(ARGS) --odir chacha-spec-vec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> chacha-spec-vec/Spec_Chacha20_vec.ml
	$(OCAMLOPT) -I chacha-spec-vec $(OCAML_INCLUDES) $(addprefix chacha-spec-vec/, $(EXTRACTED)) chacha-spec-vec/Combinators.ml chacha-spec-vec/Spec_Lib.ml chacha-spec-vec/Spec_CTR.ml chacha-spec-vec/Spec_Chacha20_vec.ml -o chacha20-vec.exe
	./chacha20-vec.exe

chacha20-vec2.exe: Spec.Chacha20_vec2.fst
	$(MAKE) -C ../code/lib/ml MEM=HST
	mkdir -p chacha-spec-vec2
	$(FSTAR) $(ARGS) --odir chacha-spec-vec2 $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> chacha-spec-vec2/Spec_Chacha20_vec2.ml
	$(OCAMLOPT) -I chacha-spec-vec2 $(OCAML_INCLUDES) $(addprefix chacha-spec-vec2/, $(EXTRACTED)) chacha-spec-vec2/Combinators.ml chacha-spec-vec2/Spec_Lib.ml chacha-spec-vec2/Spec_CTR.ml chacha-spec-vec2/Spec_Chacha20_vec2.ml -o chacha20-vec2.exe
	./chacha20-vec2.exe

chacha20-vec2-ml:
	$(OCAMLOPT) -I chacha-spec-vec2 $(OCAML_INCLUDES) $(addprefix chacha-spec-vec2/, $(EXTRACTED)) chacha-spec-vec2/Combinators.ml chacha-spec-vec2/Spec_Lib.ml chacha-spec-vec2/Spec_CTR.ml chacha-spec-vec2/Spec_Chacha20_vec2.ml -o chacha20-vec2.exe
	./chacha20-vec2.exe

chacha20-vec256.exe: Spec.Chacha20_vec256.fst
	$(MAKE) -C ../code/lib/ml MEM=HST
	mkdir -p chacha-spec-vec256
	$(FSTAR) $(ARGS) --odir chacha-spec-vec256 $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> chacha-spec-vec256/Spec_Chacha20_vec256.ml
	$(OCAMLOPT) -I chacha-spec-vec256 $(OCAML_INCLUDES) $(addprefix chacha-spec-vec256/, $(EXTRACTED)) chacha-spec-vec256/Combinators.ml chacha-spec-vec256/Spec_Lib.ml chacha-spec-vec256/Spec_CTR.ml chacha-spec-vec256/Spec_Chacha20_vec256.ml -o chacha20-vec256.exe
	./chacha20-vec256.exe

chacha20-vec3-ml:
	$(OCAMLOPT) -I chacha-spec-vec3 $(OCAML_INCLUDES) $(addprefix chacha-spec-vec3/, $(EXTRACTED)) chacha-spec-vec3/Combinators.ml chacha-spec-vec3/Spec_Lib.ml chacha-spec-vec3/Spec_CTR.ml chacha-spec-vec3/Spec_Chacha20_vec256.ml -o chacha20-vec256.exe
	./chacha20-vec256.exe

salsa20.exe: Spec.Salsa20.fst
	$(MAKE) -C ../code/lib/ml MEM=HST
	mkdir -p salsa-spec
	$(FSTAR) $(ARGS) --odir salsa-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else failwith "Test failed\n")' >> salsa-spec/Spec_Salsa20.ml
	$(OCAMLOPT) -I salsa-spec $(OCAML_INCLUDES) $(addprefix salsa-spec/, $(EXTRACTED)) salsa-spec/C_Loops.ml salsa-spec/Spec_Lib.ml salsa-spec/Spec_CTR.ml salsa-spec/Spec_Salsa20.ml -o salsa20.exe
	./salsa20.exe

secretbox.exe: Spec.HSalsa20.fst Spec.SecretBox.fst
	$(MAKE) -C ../code/lib/ml MEM=HST
	mkdir -p secretbox-spec
	$(FSTAR) $(ARGS) --odir secretbox-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else failwith "Test failed\n")' >> secretbox-spec/Spec_SecretBox.ml
	$(OCAMLOPT) -I secretbox-spec $(OCAML_INCLUDES) $(addprefix secretbox-spec/, $(EXTRACTED)) secretbox-spec/C_Loops.ml secretbox-spec/Spec_Lib.ml secretbox-spec/Spec_CTR.ml secretbox-spec/Spec_Salsa20.ml secretbox-spec/Spec_HSalsa20.ml secretbox-spec/Spec_Poly1305_Lemmas.ml secretbox-spec/Spec_Poly1305.ml secretbox-spec/Spec_SecretBox.ml -o secretbox.exe
	./secretbox.exe

chacha20poly1305.exe: Spec.Chacha20Poly1305.fst
	$(MAKE) -C ../code/lib/ml MEM=HST
	mkdir -p chacha-poly-spec
	$(FSTAR) $(ARGS) --odir chacha-poly-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else failwith "Test failed\n")' >> chacha-poly-spec/Spec_Chacha20Poly1305.ml
	$(OCAMLOPT) -I chacha-poly-spec $(OCAML_INCLUDES) $(addprefix chacha-poly-spec/, $(EXTRACTED)) chacha-poly-spec/C_Loops.ml chacha-poly-spec/Spec_Lib.ml chacha-poly-spec/Spec_CTR.ml chacha-poly-spec/Spec_Chacha20.ml chacha-poly-spec/Spec_Poly1305_Lemmas.ml chacha-poly-spec/Spec_Poly1305.ml chacha-poly-spec/Spec_Chacha20Poly1305.ml -o chacha20poly1305.exe
	./chacha20poly1305.exe


cryptobox.exe: Spec.HSalsa20.fst Spec.SecretBox.fst Spec.Curve25519.fst Spec.CryptoBox.fst
	$(MAKE) -C ../code/lib/ml MEM=HST
	mkdir -p cryptobox-spec
	$(FSTAR) $(ARGS) --odir cryptobox-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> cryptobox-spec/Spec_CryptoBox.ml
	$(OCAMLOPT) -I cryptobox-spec $(OCAML_INCLUDES) $(addprefix cryptobox-spec/, $(EXTRACTED)) cryptobox-spec/Combinators.ml cryptobox-spec/Spec_Lib.ml cryptobox-spec/Spec_CTR.ml cryptobox-spec/Spec_Salsa20.ml cryptobox-spec/Spec_HSalsa20.ml cryptobox-spec/Spec_Poly1305.ml cryptobox-spec/Spec_SecretBox.ml cryptobox-spec/Spec_Curve25519.ml cryptobox-spec/Spec_CryptoBox.ml -o cryptobox.exe
	./cryptobox.exe

clean:
	$(MAKE) -C ../code/lib/ml clean
	rm -rf *.cmi *.cmo *.cmx *.o *~ *.out *.exe poly-spec chacha-spec secretbox-spec chacha-poly-spec salsa-spec gf128-spec curve25519-spec cryptobox-spec
