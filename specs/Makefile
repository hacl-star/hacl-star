include ../Makefile.include

.PHONY=lib all

FSTAR_INCLUDES+=--include $(HACL_HOME)/specs/lemmas

# OCaml variables
OCAMLOPT := $(OCAMLOPT) -w -8-20-26-28-10
OCAML_INCLUDES=-I ../code/lib/ml ../code/lib/ml/hacllib.cmxa

all: lib
	$(MAKE)	poly1305.exe chacha20.exe salsa20.exe chacha20poly1305.exe gf128.exe ed25519.exe curve25519.exe sha2_256.exe sha2_384.exe sha2_512.exe hmac_sha2_256.exe hmac_sha2_384.exe hmac_sha2_512.exe sha2.exe hmac_sha2.exe

lib:
	$(MAKE) -C ../code/lib/ml


EXTRACTED=FStar_Seq_Base.ml FStar_Seq.ml FStar_Seq_Properties.ml FStar_Math_Lib.ml FStar_BitVector.ml FStar_UInt.ml

NOEXTRACT=$(FSTAR_DEFAULT_ARGS) $(addprefix --no_extract Hacl., UInt64 UInt32 UInt8)

SPEC_FILES=	Spec.Chacha20.fst \
		Spec.Chacha20_vec.fst \
		Spec.Chacha20Poly1305.fst \
		Spec.CTR.fst \
		Spec.Curve25519.fst \
		Spec.GaloisField.fst \
		Spec.GF128.fst \
		Spec.HSalsa20.fst \
		Spec.Lib.fst \
		Spec.Poly1305.fst \
		Spec.Salsa20.fst \
		Spec.SHA2.fst \
		Spec.SHA2_256.fst \
		Spec.SHA2_384.fst \
		Spec.SHA2_512.fst \
		Spec.HMAC.fst \
		Spec.Ed25519.fst

hints: $(addsuffix .hints, $(SPEC_FILES))
verify: $(addsuffix -verify, $(SPEC_FILES))
all-hints: hints
all-ver: verify

FSTAR_EXTRACT=$(FSTAR) --codegen OCaml --lax $(NOEXTRACT)

gf128.exe: Spec.GF128.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p gf128-spec
	$(FSTAR_EXTRACT) --odir gf128-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else failwith "Test failed\n")' >> gf128-spec/Spec_GF128.ml
	$(OCAMLOPT) -I gf128-spec $(OCAML_INCLUDES) gf128-spec/FStar_Endianness.ml gf128-spec/Spec_GaloisField.ml gf128-spec/Spec_GF128.ml -o gf128.exe
	./gf128.exe

poly1305.exe: Spec.Poly1305.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p poly-spec
	$(FSTAR_EXTRACT) --odir poly-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else failwith "Test failed\n")' >> poly-spec/Spec_Poly1305.ml
	$(OCAMLOPT) -I poly-spec $(OCAML_INCLUDES) poly-spec/FStar_Endianness.ml poly-spec/Spec_Poly1305_Lemmas.ml poly-spec/Spec_Poly1305.ml -o poly1305.exe
	./poly1305.exe

curve25519.exe: Spec.Curve25519.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p curve25519-spec
	$(FSTAR_EXTRACT) --odir curve25519-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else failwith "Test failed\n")' >> curve25519-spec/Spec_Curve25519.ml
	$(OCAMLOPT) -I curve25519-spec $(OCAML_INCLUDES) curve25519-spec/FStar_Endianness.ml curve25519-spec/Spec_Loops.ml curve25519-spec/Spec_Lib.ml curve25519-spec/Spec_Curve25519.ml -o curve25519.exe
	./curve25519.exe

chacha20.exe: Spec.Chacha20.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p chacha-spec
	$(FSTAR_EXTRACT) --odir chacha-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else failwith "Test failed\n")' >> chacha-spec/Spec_Chacha20.ml
	$(OCAMLOPT) -I chacha-spec $(OCAML_INCLUDES) chacha-spec/FStar_Endianness.ml chacha-spec/Spec_Loops.ml chacha-spec/Seq_Create.ml chacha-spec/Spec_Lib.ml chacha-spec/Spec_CTR.ml chacha-spec/Spec_Chacha20.ml -o chacha20.exe
	./chacha20.exe

salsa20.exe: Spec.Salsa20.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p salsa-spec
	$(FSTAR_EXTRACT) --odir salsa-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else failwith "Test failed\n")' >> salsa-spec/Spec_Salsa20.ml
	$(OCAMLOPT) -I salsa-spec $(OCAML_INCLUDES) salsa-spec/FStar_Endianness.ml salsa-spec/Spec_Loops.ml salsa-spec/Seq_Create.ml salsa-spec/Spec_Lib.ml salsa-spec/Spec_CTR.ml salsa-spec/Spec_Salsa20.ml -o salsa20.exe
	./salsa20.exe

chacha20poly1305.exe: Spec.Chacha20Poly1305.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p chacha-poly-spec
	$(FSTAR_EXTRACT) --odir chacha-poly-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else failwith "Test failed\n")' >> chacha-poly-spec/Spec_Chacha20Poly1305.ml
	$(OCAMLOPT) -I chacha-poly-spec $(OCAML_INCLUDES) chacha-poly-spec/FStar_Endianness.ml chacha-poly-spec/Spec_Loops.ml chacha-poly-spec/Seq_Create.ml chacha-poly-spec/Spec_Lib.ml chacha-poly-spec/Spec_CTR.ml chacha-poly-spec/Spec_Chacha20.ml chacha-poly-spec/Spec_Poly1305_Lemmas.ml chacha-poly-spec/Spec_Poly1305.ml chacha-poly-spec/Spec_Chacha20Poly1305.ml -o chacha20poly1305.exe
	./chacha20poly1305.exe

sha2generic.exe: Spec.SHA2.Test.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p sha2-spec
	$(FSTAR_EXTRACT) --odir sha2-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> sha2-spec/Spec_SHA2_Test.ml
	$(OCAMLOPT) -I sha2-spec $(OCAML_INCLUDES) sha2-spec/FStar_Endianness.ml sha2-spec/Spec_Loops.ml sha2-spec/Spec_Lib.ml sha2-spec/Seq_Create.ml sha2-spec/Spec_SHA2_Generic.ml sha2-spec/Spec_SHA2_Test.ml -o sha2generic.exe
	./sha2generic.exe

sha2.exe: Spec.SHA2.Test.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p sha2-spec
	$(FSTAR_EXTRACT) --odir sha2-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> sha2-spec/Spec_SHA2_Test.ml
	$(OCAMLOPT) -I sha2-spec $(OCAML_INCLUDES) sha2-spec/FStar_Endianness.ml sha2-spec/Spec_Loops.ml sha2-spec/Spec_Lib.ml sha2-spec/Seq_Create.ml sha2-spec/Spec_SHA2.ml sha2-spec/Spec_SHA2_Test.ml -o sha2.exe
	./sha2.exe

sha2_256.exe: Spec.SHA2_256.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p sha2_256-spec
	$(FSTAR_EXTRACT) --odir sha2_256-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> sha2_256-spec/Spec_SHA2_256.ml
	$(OCAMLOPT) -I sha2_256-spec $(OCAML_INCLUDES) sha2_256-spec/FStar_Endianness.ml sha2_256-spec/Spec_Loops.ml sha2_256-spec/Spec_Lib.ml sha2_256-spec/Seq_Create.ml sha2_256-spec/Spec_SHA2_256.ml -o sha2_256.exe
	./sha2_256.exe

sha2_384.exe: Spec.SHA2_384.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p sha2_384-spec
	$(FSTAR_EXTRACT) --odir sha2_384-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> sha2_384-spec/Spec_SHA2_384.ml
	$(OCAMLOPT) -I sha2_384-spec $(OCAML_INCLUDES) sha2_384-spec/FStar_Endianness.ml sha2_384-spec/Spec_Loops.ml sha2_384-spec/Spec_Lib.ml sha2_384-spec/Seq_Create.ml sha2_384-spec/Spec_SHA2_384.ml -o sha2_384.exe
	./sha2_384.exe

sha2_512.exe: Spec.SHA2_512.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p sha2_512-spec
	$(FSTAR_EXTRACT) --odir sha2_512-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> sha2_512-spec/Spec_SHA2_512.ml
	$(OCAMLOPT) -I sha2_512-spec $(OCAML_INCLUDES) sha2_512-spec/FStar_Endianness.ml sha2_512-spec/Spec_Loops.ml sha2_512-spec/Spec_Lib.ml sha2_512-spec/Seq_Create.ml sha2_512-spec/Spec_SHA2_512.ml -o sha2_512.exe
	./sha2_512.exe

hmac_sha2.exe: Spec.HMAC.Test.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p hmac-sha2-spec
	$(FSTAR_EXTRACT) --odir hmac-sha2-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> hmac-sha2-spec/Spec_HMAC_Test.ml
	$(OCAMLOPT) -I hmac-sha2-spec $(OCAML_INCLUDES) hmac-sha2-spec/FStar_Endianness.ml hmac-sha2-spec/Spec_Loops.ml hmac-sha2-spec/Spec_Lib.ml hmac-sha2-spec/Seq_Create.ml hmac-sha2-spec/Spec_SHA2.ml hmac-sha2-spec/Spec_HMAC.ml hmac-sha2-spec/Spec_HMAC_Test.ml -o hmac_sha2.exe
	./hmac_sha2.exe

hmac_sha2_256.exe: Spec.HMAC.SHA2_256.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p hmac-sha2_256-spec
	$(FSTAR_EXTRACT) --odir hmac-sha2_256-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> hmac-sha2_256-spec/Spec_HMAC_SHA2_256.ml
	$(OCAMLOPT) -I hmac-sha2_256-spec $(OCAML_INCLUDES) hmac-sha2_256-spec/FStar_Endianness.ml hmac-sha2_256-spec/Spec_Loops.ml hmac-sha2_256-spec/Spec_Lib.ml hmac-sha2_256-spec/Seq_Create.ml hmac-sha2_256-spec/Spec_SHA2_256.ml hmac-sha2_256-spec/Spec_HMAC_SHA2_256.ml -o hmac_sha2_256.exe
	./hmac_sha2_256.exe

hmac_sha2_384.exe: Spec.HMAC.SHA2_384.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p hmac-sha2_384-spec
	$(FSTAR_EXTRACT) --odir hmac-sha2_384-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> hmac-sha2_384-spec/Spec_HMAC_SHA2_384.ml
	$(OCAMLOPT) -I hmac-sha2_384-spec $(OCAML_INCLUDES) hmac-sha2_384-spec/FStar_Endianness.ml hmac-sha2_384-spec/Spec_Loops.ml hmac-sha2_384-spec/Spec_Lib.ml hmac-sha2_384-spec/Seq_Create.ml hmac-sha2_384-spec/Spec_SHA2_384.ml hmac-sha2_384-spec/Spec_HMAC_SHA2_384.ml -o hmac_sha2_384.exe
	./hmac_sha2_384.exe

hmac_sha2_512.exe: Spec.HMAC.SHA2_512.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p hmac-sha2_512-spec
	$(FSTAR_EXTRACT) --odir hmac-sha2_512-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> hmac-sha2_512-spec/Spec_HMAC_SHA2_512.ml
	$(OCAMLOPT) -I hmac-sha2_512-spec $(OCAML_INCLUDES) hmac-sha2_512-spec/FStar_Endianness.ml hmac-sha2_512-spec/Spec_Loops.ml hmac-sha2_512-spec/Spec_Lib.ml hmac-sha2_512-spec/Seq_Create.ml hmac-sha2_512-spec/Spec_SHA2_512.ml hmac-sha2_512-spec/Spec_HMAC_SHA2_512.ml -o hmac_sha2_512.exe
	./hmac_sha2_512.exe

ed25519.exe: Spec.SHA512.fst Spec.Ed25519.fst
	$(MAKE) -C ../code/lib/ml
	mkdir -p ed25519-spec
	$(FSTAR_EXTRACT) --odir ed25519-spec $^
	@echo 'let _ = print_string (if test() then "SUCCESS\n" else "FAILURE\n")' >> ed25519-spec/Spec_Ed25519.ml
	$(OCAMLOPT) -I ed25519-spec  $(OCAML_INCLUDES) $(addprefix ed25519-spec/, FStar_Endianness.ml Spec_Loops.ml Spec_Lib.ml Spec_Curve25519.ml Seq_Create.ml Spec_SHA2_512.ml Spec_SHA512.ml Spec_Ed25519.ml) -o ed25519.exe
	./ed25519.exe
clean:
	$(MAKE) -C ../code/lib/ml clean
	rm -rf *.cmi *.cmo *.cmx *.o *~ *.out *.exe poly-spec chacha-spec chacha-poly-spec salsa-spec gf128-spec curve25519-spec sha2-spec sha2_256-spec sha2_384-spec sha2_512-spec hmac-sha2-spec hmac-sha2_256-spec hmac-sha2_384-spec hmac-sha2_512-spec ed25519-spec
