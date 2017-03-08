include ../code/Makefile.include

.PHONY=lib all

# OCaml variables
OCAMLOPT := $(OCAMLOPT) -w -8-20-26-28-10
OCAML_INCLUDES=-I ../code/lib/ml ../code/lib/ml/hacllib.cmxa

all: lib
	$(MAKE)	poly1305.exe chacha20.exe salsa20.exe chacha20poly1305.exe gf128.exe ed25519.exe curve25519.exe sha2_256.exe sha2_512.exe

lib:
	$(MAKE) -C ../code/lib/ml


EXTRACTED=FStar_Seq_Base.ml FStar_Seq.ml FStar_Seq_Properties.ml FStar_Math_Lib.ml FStar_BitVector.ml FStar_UInt.ml  

NOEXTRACT=$(FSTAR_DEFAULT_ARGS) $(addprefix --no_extract Hacl., UInt64 UInt32 UInt8)

OTHERFLAGS+=--codegen OCaml --lax $(NOEXTRACT)

SPEC_FILES=	Spec.Chacha20.Lemmas.fst \
		Spec.Chacha20.fst \
		Spec.Chacha20_vec.fst \
		Spec.Chacha20Poly1305.fst \
		Spec.CTR.fst \
		Spec.Curve25519.Lemmas.fst \
		Spec.Curve25519.fst \
		Spec.GaloisField.fst \
		Spec.GF128.fst \
		Spec.HSalsa20.fst \
		Spec.Lib.fst \
		Spec.Poly1305.fst \
		Spec.Poly1305.Lemmas.fst \
		Spec.Salsa20.fst \
		Spec.SHA2_256.fst \
		Spec.SHA2_384.fst \
		Spec.SHA2_512.fst \
		Spec.Ed25519.fst

hints: $(addsuffix .hints, $(SPEC_FILES))
verify: $(addsuffix -verify, $(SPEC_FILES))
all-hints: hints
all-ver: verify

gf128.exe: Spec.GF128.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p gf128-spec
	$(FSTAR) --odir gf128-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else failwith "Test failed\n")' >> gf128-spec/Spec_GF128.ml
	$(OCAMLOPT) -I gf128-spec $(OCAML_INCLUDES) gf128-spec/FStar_Endianness.ml gf128-spec/Spec_GaloisField.ml gf128-spec/Spec_GF128.ml -o gf128.exe
	./gf128.exe

poly1305.exe: Spec.Poly1305.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p poly-spec
	$(FSTAR) --odir poly-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else failwith "Test failed\n")' >> poly-spec/Spec_Poly1305.ml
	$(OCAMLOPT) -I poly-spec $(OCAML_INCLUDES) poly-spec/FStar_Endianness.ml poly-spec/Spec_Poly1305_Lemmas.ml poly-spec/Spec_Poly1305.ml -o poly1305.exe
	./poly1305.exe

curve25519.exe: Spec.Curve25519.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p curve25519-spec
	$(FSTAR) --odir curve25519-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else failwith "Test failed\n")' >> curve25519-spec/Spec_Curve25519.ml
	$(OCAMLOPT) -I curve25519-spec $(OCAML_INCLUDES) curve25519-spec/FStar_Endianness.ml curve25519-spec/Spec_Loops.ml curve25519-spec/Spec_Lib.ml curve25519-spec/Spec_Curve25519.ml -o curve25519.exe
	./curve25519.exe

chacha20.exe: Spec.Chacha20.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p chacha-spec
	$(FSTAR) --odir chacha-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else failwith "Test failed\n")' >> chacha-spec/Spec_Chacha20.ml
	$(OCAMLOPT) -I chacha-spec $(OCAML_INCLUDES) chacha-spec/FStar_Endianness.ml chacha-spec/Spec_Loops.ml chacha-spec/Seq_Create.ml chacha-spec/Spec_Lib.ml chacha-spec/Spec_CTR.ml chacha-spec/Spec_Chacha20.ml -o chacha20.exe
	./chacha20.exe

salsa20.exe: Spec.Salsa20.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p salsa-spec
	$(FSTAR) --odir salsa-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else failwith "Test failed\n")' >> salsa-spec/Spec_Salsa20.ml
	$(OCAMLOPT) -I salsa-spec $(OCAML_INCLUDES) salsa-spec/FStar_Endianness.ml salsa-spec/Spec_Loops.ml salsa-spec/Seq_Create.ml salsa-spec/Spec_Lib.ml salsa-spec/Spec_CTR.ml salsa-spec/Spec_Salsa20.ml -o salsa20.exe
	./salsa20.exe

chacha20poly1305.exe: Spec.Chacha20Poly1305.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p chacha-poly-spec
	$(FSTAR) --odir chacha-poly-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else failwith "Test failed\n")' >> chacha-poly-spec/Spec_Chacha20Poly1305.ml
	$(OCAMLOPT) -I chacha-poly-spec $(OCAML_INCLUDES) chacha-poly-spec/FStar_Endianness.ml chacha-poly-spec/Spec_Loops.ml chacha-poly-spec/Seq_Create.ml chacha-poly-spec/Spec_Lib.ml chacha-poly-spec/Spec_CTR.ml chacha-poly-spec/Spec_Chacha20.ml chacha-poly-spec/Spec_Poly1305_Lemmas.ml chacha-poly-spec/Spec_Poly1305.ml chacha-poly-spec/Spec_Chacha20Poly1305.ml -o chacha20poly1305.exe
	./chacha20poly1305.exe

sha2_256.exe: Spec.SHA2_256.fst
	$(MAKE) lib
	mkdir -p sha2-spec
	$(FSTAR) --odir sha2-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> sha2-spec/Spec_SHA2_256.ml
	$(OCAMLOPT) -I sha2-spec $(OCAML_INCLUDES) sha2-spec/FStar_Endianness.ml sha2-spec/Spec_Loops.ml sha2-spec/Spec_Lib.ml sha2-spec/Seq_Create.ml sha2-spec/Spec_SHA2_256.ml -o sha2_256.exe
	./sha2_256.exe

sha2_384.exe: Spec.SHA2_384.fst
	$(MAKE) lib
	mkdir -p sha2-spec
	$(FSTAR) --odir sha2-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> sha2-spec/Spec_SHA2_384.ml
	$(OCAMLOPT) -I sha2-spec $(OCAML_INCLUDES) sha2-spec/FStar_Endianness.ml sha2-spec/Spec_Loops.ml sha2-spec/Spec_Lib.ml sha2-spec/Seq_Create.ml sha2-spec/Spec_SHA2_384.ml -o sha2_384.exe
	./sha2_384.exe

sha2_512.exe: Spec.SHA2_512.fst
	$(MAKE) lib
	mkdir -p sha2-spec
	$(FSTAR) --odir sha2-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> sha2-spec/Spec_SHA2_512.ml
	$(OCAMLOPT) -I sha2-spec $(OCAML_INCLUDES) sha2-spec/FStar_Endianness.ml sha2-spec/Spec_Loops.ml sha2-spec/Spec_Lib.ml sha2-spec/Seq_Create.ml sha2-spec/Spec_SHA2_512.ml -o sha2_512.exe
	./sha2_512.exe

hmac_sha2_256.exe: Spec.HMAC.SHA2_256.fst
	$(MAKE) lib
	mkdir -p hmac-sha2-spec
	$(FSTAR) --odir hmac-sha2-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> hmac-sha2-spec/Spec_HMAC_SHA2_256.ml
	$(OCAMLOPT) -I hmac-sha2-spec $(OCAML_INCLUDES) hmac-sha2-spec/FStar_Endianness.ml hmac-sha2-spec/Spec_Loops.ml hmac-sha2-spec/Spec_Lib.ml hmac-sha2-spec/Seq_Create.ml hmac-sha2-spec/Spec_SHA2_256.ml hmac-sha2-spec/Spec_HMAC_SHA2_256.ml -o hmac_sha2_256.exe
	./hmac_sha2_256.exe

ed25519.exe: Spec.SHA512.fst Spec.Ed25519.fst
	$(MAKE) lib
	mkdir -p ed25519-spec
	$(FSTAR) --odir ed25519-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> ed25519-spec/Spec_Ed25519.ml
	$(OCAMLOPT) -I ed25519-spec  $(OCAML_INCLUDES) $(addprefix ed25519-spec/, FStar_Endianness.ml Spec_Loops.ml Spec_Lib.ml Spec_Curve25519.ml Seq_Create.ml Spec_SHA2_512.ml Spec_SHA512.ml Spec_Ed25519.ml) -o ed25519.exe
	./ed25519.exe

cryptobox.exe: Spec.HSalsa20.fst Spec.SecretBox.fst Spec.Curve25519.fst Spec.CryptoBox.fst
	$(MAKE) -C ../code/lib/ml MEM=HST
	mkdir -p cryptobox-spec
	$(FSTAR) $(ARGS) --odir cryptobox-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> cryptobox-spec/Spec_CryptoBox.ml
	$(OCAMLOPT) -I cryptobox-spec $(OCAML_INCLUDES) $(addprefix cryptobox-spec/, $(EXTRACTED)) cryptobox-spec/Combinators.ml cryptobox-spec/Spec_Lib.ml cryptobox-spec/Spec_CTR.ml cryptobox-spec/Spec_Salsa20.ml cryptobox-spec/Spec_HSalsa20.ml cryptobox-spec/Spec_Poly1305.ml cryptobox-spec/Spec_SecretBox.ml cryptobox-spec/Spec_Curve25519.ml cryptobox-spec/Spec_CryptoBox.ml -o cryptobox.exe
	./cryptobox.exe

clean:
	$(MAKE) -C ../code/lib/ml clean
	rm -rf *.cmi *.cmo *.cmx *.o *~ *.out *.exe poly-spec chacha-spec chacha-poly-spec salsa-spec gf128-spec curve25519-spec sha2-spec hmac-sha2-spec ed25519-spec
