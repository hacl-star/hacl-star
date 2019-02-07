FSTAR_HOME=$(HACL_HOME)/../FStar

include ../Makefile.include

.PHONY=all test

FSTAR_INCLUDES+= \
	--include $(HACL_HOME)/lib \
	--include $(HACL_HOME)/lib/fst \
	--include $(HACL_HOME)/specs/lemmas \
	--expose_interfaces

SPEC_FILES=	Spec.Chacha20.fst \
		Spec.Poly1305.fst \
		Spec.Chacha20.fst \
		Spec.Chacha20Poly1305.fst \
		Spec.Curve25519.fst \
		Spec.Curve448.fst \
		Spec.Salsa20.fst \
		Spec.Ed25519.fst \
		Spec.Chacha20_vec.fst \
		Spec.GaloisField.fst \
		Spec.GF128.fst \
		Spec.AES.fst \
		Spec.AESGCM.fst \
		Spec.SHA2.fst \
		Spec.SHA2.Constants.fst \
		Spec.SHA2.New.fst \
		Spec.HMAC.fst \
		Spec.HKDF.fst \
		Spec.ECIES.fst \
		Spec.HSalsa20.fst

LIBS = Lib.IntTypes.fst Lib.RawIntTypes.fst Lib.NatMod.fst Lib.LoopCombinators.fst Lib.Sequence.fst Lib.ByteSequence.fst Lib.PrintSequence.fst
LIBS_FILES= $(addprefix ../lib/fst/, $(LIBS))
LIBS_ML = Lib_IntTypes.ml Lib_RawIntTypes.ml Lib_NatMod.ml Lib_LoopCombinators.ml Lib_Sequence.ml Lib_ByteSequence.ml Lib_PrintSequence.ml
LIBS_EX = $(addprefix --extract_module , $(LIBS:.fst=))

#
# Main targets
#

hints: $(addsuffix .hints, $(SPEC_FILES))
verify: $(addsuffix -verify, $(SPEC_FILES))

all: test

test: test-unified-target test-individual-target

test-unified-target: Chacha20.exe Curve25519.exe Curve448.exe SHA2.exe Blake2.exe
test-individual-target: Poly1305.exe Chacha20Poly1305.exe Ed25519.exe hmac.exe hkdf.exe argon2i.exe kyber.exe aes.exe gf128.exe aes128gcm.exe rsapss.exe sha3.exe ecies.exe

clean:
	rm -rf *.cmi *.cmo *.cmx *.o *~ *.out *.exe *-ml

#
# Primitive targets
#

%.exe: $(LIBS_FILES) Spec.%.fst tests/Spec.%.Test.fst
	mkdir -p $*-ml
	$(FSTAR) --codegen OCaml --lax $(LIBS_EX) --extract_module Spec.$* --extract_module Spec.$*.Test --odir $*-ml $^
	@echo 'let _ = test()' >> $*-ml/Spec_$*_Test.ml
	$(OCAMLOPT) -I $*-ml $(addprefix $*-ml/, $(LIBS_ML))  $*-ml/Spec_$*.ml $*-ml/Spec_$*_Test.ml -o $*.exe
	./$*.exe

# Under CI
dh.exe: $(LIBS_FILES) Spec.Curve25519.fst Spec.Curve448.fst Spec.DH.fst tests/Spec.DH.Test.fst
	mkdir -p dh-ml
	$(FSTAR) --codegen OCaml --lax $(LIBS_EX) --extract_module Spec.Curve25519 --extract_module Spec.Curve448 --extract_module Spec.DH --extract_module Spec.DH.Test --odir dh-ml $^
	@echo 'let _ = test()' >> dh-ml/Spec_DH_Test.ml
	$(OCAMLOPT) -I dh-ml $(addprefix dh-ml/, $(LIBS_ML)) dh-ml/Spec_Curve25519.ml dh-ml/Spec_Curve448.ml dh-ml/Spec_DH.ml dh-ml/Spec_DH_Test.ml -o dh.exe
	./dh.exe

# Under CI
Salsa20.exe: $(LIBS_FILES) Spec.CTR.fst Spec.Salsa20.fst tests/Spec.Salsa20.Test.fst
	mkdir -p Salsa20-ml
	$(FSTAR) --codegen OCaml --lax $(LIBS_EX) --extract_module Spec.CTR --extract_module Spec.Salsa20 --extract_module Spec.Salsa20.Test --odir Salsa20-ml $^
	@echo 'let _ = test()' >> Salsa20-ml/Spec_Salsa20_Test.ml
	$(OCAMLOPT) -I Salsa20-ml $(addprefix Salsa20-ml/, $(LIBS_ML)) Salsa20-ml/Spec_CTR.ml Salsa20-ml/Spec_Salsa20.ml Salsa20-ml/Spec_Salsa20_Test.ml -o Salsa20.exe
	./Salsa20.exe

# Under CI
Chacha20Poly1305.exe: $(LIBS_FILES) Spec.Chacha20.fst Spec.Poly1305.fst Spec.Chacha20Poly1305.fst tests/Spec.Chacha20Poly1305.Test.fst
	mkdir -p Chacha20Poly1305-ml
	$(FSTAR) --codegen OCaml --lax $(LIBS_EX) --extract_module Spec.Chacha20 --extract_module Spec.Poly1305 --extract_module Spec.Chacha20Poly1305 --extract_module Spec.Chacha20Poly1305.Test --odir Chacha20Poly1305-ml $^
	@echo 'let _ = test()' >> Chacha20Poly1305-ml/Spec_Chacha20Poly1305_Test.ml
	$(OCAMLOPT) -I Chacha20Poly1305-ml $(addprefix Chacha20Poly1305-ml/, $(LIBS_ML)) Chacha20Poly1305-ml/Spec_Chacha20.ml Chacha20Poly1305-ml/Spec_Poly1305.ml Chacha20Poly1305-ml/Spec_Chacha20Poly1305.ml Chacha20Poly1305-ml/Spec_Chacha20Poly1305_Test.ml -o Chacha20Poly1305.exe
	./Chacha20Poly1305.exe

# Under CI
Ed25519.exe: $(LIBS_FILES) Spec.SHA2.fst Spec.Curve25519.fst Spec.Ed25519.fst tests/Spec.Ed25519.Test.fst
	mkdir -p Ed25519-ml
	$(FSTAR) --codegen OCaml --lax $(LIBS_EX) --extract_module Spec.SHA2 --extract_module Spec.Curve25519 --extract_module Spec.Ed25519 --extract_module Spec.Ed25519.Test --odir Ed25519-ml $^
	@echo 'let _ = test()' >> Ed25519-ml/Spec_Ed25519_Test.ml
	$(OCAMLOPT) -I Ed25519-ml $(addprefix Ed25519-ml/, $(LIBS_ML)) Ed25519-ml/Spec_SHA2.ml Ed25519-ml/Spec_Curve25519.ml Ed25519-ml/Spec_Ed25519.ml Ed25519-ml/Spec_Ed25519_Test.ml -o Ed25519.exe
	./Ed25519.exe

# Under CI
gf128.exe: $(LIBS_FILES) Spec.GaloisField.fst Spec.GF128.fst tests/Spec.GF128.Test.fst
	mkdir -p gf128-ml
	$(FSTAR) --codegen OCaml --lax $(LIBS_EX) --extract_module Spec.GaloisField --extract_module Spec.GF128 --extract_module Spec.GF128.Test --odir gf128-ml $^
	@echo 'let _ = test()' >> gf128-ml/Spec_GF128_Test.ml
	$(OCAMLOPT) -I gf128-ml $(OCAML_INCLUDES) $(addprefix gf128-ml/, $(LIBS_ML)) gf128-ml/Spec_GaloisField.ml gf128-ml/Spec_GF128.ml gf128-ml/Spec_GF128_Test.ml -o gf128.exe
	./gf128.exe

# Under CI
aes.exe: $(LIBS_FILES) Spec.GaloisField.fst Spec.AES.fst tests/Spec.AES.Test.fst
	mkdir -p aes-ml
	$(FSTAR) --codegen OCaml --lax $(LIBS_EX) --extract_module Spec.GaloisField --extract_module Spec.AES --extract_module Spec.AES.Test --odir aes-ml $^
	@echo 'let _ = test()' >> aes-ml/Spec_AES_Test.ml
	$(OCAMLOPT) -I aes-ml $(OCAML_INCLUDES) $(addprefix aes-ml/, $(LIBS_ML)) aes-ml/Spec_GaloisField.ml aes-ml/Spec_AES.ml aes-ml/Spec_AES_Test.ml -o aes.exe
	./aes.exe

# Under CI
aes128gcm.exe: $(LIBS_FILES) Spec.GaloisField.fst Spec.AES.fst Spec.GF128.fst Spec.AES128_GCM.fst tests/Spec.AES128_GCM.Test.fst
	mkdir -p aesgcm-ml
	$(FSTAR) --codegen OCaml --lax $(LIBS_EX) --extract_module Spec.GaloisField --extract_module Spec.AES --extract_module Spec.AES128_GCM  --extract_module Spec.AES128_GCM.Test --extract_module Spec.GF128 --odir aesgcm-ml $^
	@echo 'let _ = test()' >> aesgcm-ml/Spec_AES128_GCM_Test.ml
	$(OCAMLOPT) -I aesgcm-ml $(OCAML_INCLUDES) $(addprefix aesgcm-ml/, $(LIBS_ML)) aesgcm-ml/Spec_GaloisField.ml aesgcm-ml/Spec_AES.ml aesgcm-ml/Spec_GF128.ml aesgcm-ml/Spec_AES128_GCM.ml aesgcm-ml/Spec_AES128_GCM_Test.ml -o aes128gcm.exe
	./aes128gcm.exe

# Not Under CI
aes128cbc.exe: $(LIBS_FILES) Spec.GaloisField.fst Spec.AES.fst Spec.AES128_CBC.fst tests/Spec.AES128_CBC.Test.fst
	mkdir -p aes128cbc-ml
	$(FSTAR) --codegen OCaml --lax $(LIBS_EX) --extract_module Spec.GaloisField --extract_module Spec.AES --extract_module Spec.AES128_CBC  --extract_module Spec.AES128_CBC.Test --odir aes128cbc-ml $^
	# @echo 'let _ = test()' >> aes128cbc-ml/Spec_AES128_CBC_Test.ml
	$(OCAMLOPT) -I aes128cbc-ml $(OCAML_INCLUDES) $(addprefix aes128cbc-ml/, $(LIBS_ML)) aes128cbc-ml/Spec_GaloisField.ml aes128cbc-ml/Spec_AES.ml aes128cbc-ml/Spec_AES128_CBC.ml aes128cbc-ml/Spec_AES128_CBC_Test.ml -o aes128cbc.exe
	./aes128cbc.exe

# Under CI
kyber.exe: $(LIBS_FILES) Spec.Kyber.fst
	mkdir -p kyber-ml
	$(FSTAR) --codegen OCaml --lax $(LIBS_EX) --extract_module Spec.Kyber --odir kyber-ml $^
	@echo 'let _ = test()' >> kyber-ml/Spec_Kyber.ml
	$(OCAMLOPT) -I kyber-ml $(OCAML_INCLUDES) $(addprefix kyber-ml/, $(LIBS_ML)) kyber-ml/Spec_Kyber.ml -o kyber.exe
	./kyber.exe

# Under CI
hmac.exe: $(LIBS_FILES) Spec.SHA2.fst Spec.Hash.fst Spec.HMAC.fst tests/Spec.HMAC.Test.fst
	mkdir -p hmac-ml
	$(FSTAR) --codegen OCaml --lax $(LIBS_EX) --extract_module Spec.SHA2 --extract_module Spec.Hash --extract_module Spec.HMAC --extract_module Spec.HMAC.Test --odir hmac-ml $^
	@echo 'let _ = test()' >> hmac-ml/Spec_HMAC_Test.ml
	$(OCAMLOPT) -I hmac-ml $(OCAML_INCLUDES) $(addprefix hmac-ml/, $(LIBS_ML)) hmac-ml/Spec_SHA2.ml hmac-ml/Spec_Hash.ml hmac-ml/Spec_HMAC.ml hmac-ml/Spec_HMAC_Test.ml -o hmac.exe
	./hmac.exe

hmac_generic.exe: $(LIBS_FILES) Spec.Blake2.fst Spec.SHA2.fst Spec.Hash_Generic.fst Spec.HMAC_Generic.fst tests/Spec.HMAC_Generic.Test.fst
	mkdir -p hmac-ml
	$(FSTAR) --codegen OCaml --lax $(LIBS_EX) --extract_module Spec.SHA2 --extract_module Spec.Blake2 --extract_module Spec.Hash_Generic --extract_module Spec.HMAC_Generic --extract_module Spec.HMAC_Generic.Test --odir hmac-ml $^
	@echo 'let _ = test()' >> hmac-ml/Spec_HMAC_Generic_Test.ml
	$(OCAMLOPT) -I hmac-ml $(OCAML_INCLUDES) $(addprefix hmac-ml/, $(LIBS_ML)) hmac-ml/Spec_SHA2.ml hmac-ml/Spec_Blake2.ml hmac-ml/Spec_Hash_Generic.ml hmac-ml/Spec_HMAC_Generic.ml hmac-ml/Spec_HMAC_Generic_Test.ml -o hmac.exe
	./hmac.exe

sha2-new.exe: $(LIBS_FILES) Spec.SHA2.Constants.fst Spec.SHA2.New.fst tests/Spec.SHA2.New.Test.fst
	mkdir -p sha2-ml
	$(FSTAR) --codegen OCaml --lax $(LIBS_EX) --extract_module Spec.SHA2.Constants --extract_module Spec.SHA2.New --extract_module Spec.SHA2.New.Test --odir sha2-ml $^
	@echo 'let _ = test()' >> sha2-ml/Spec_SHA2_New_Test.ml
	$(OCAMLOPT) -I sha2-ml $(OCAML_INCLUDES) $(addprefix sha2-ml/, $(LIBS_ML)) sha2-ml/Spec_SHA2_Constants.ml sha2-ml/Spec_SHA2_New.ml sha2-ml/Spec_SHA2_New_Test.ml -o sha2-new.exe
	./sha2-new.exe

# Under CI
hkdf.exe: $(LIBS_FILES) Spec.SHA2.fst Spec.Hash.fst Spec.HMAC.fst Spec.HKDF.fst tests/Spec.HKDF.Test.fst
	mkdir -p hkdf-ml
	$(FSTAR) --codegen OCaml --lax $(LIBS_EX) --extract_module Spec.SHA2 --extract_module Spec.Hash --extract_module Spec.HMAC --extract_module Spec.HKDF --extract_module Spec.HKDF.Test --odir hkdf-ml $^
	@echo 'let _ = test()' >> hkdf-ml/Spec_HKDF_Test.ml
	$(OCAMLOPT) -I hkdf-ml $(OCAML_INCLUDES) $(addprefix hkdf-ml/, $(LIBS_ML)) hkdf-ml/Spec_SHA2.ml hkdf-ml/Spec_Hash.ml hkdf-ml/Spec_HMAC.ml hkdf-ml/Spec_HKDF.ml hkdf-ml/Spec_HKDF_Test.ml -o hkdf.exe
	./hkdf.exe

ecies.exe: $(LIBS_FILES) Spec.SHA2.fst Spec.Hash.fst Spec.HMAC.fst Spec.HKDF.fst Spec.Curve25519.fst Spec.Curve448.fst Spec.DH.fst Spec.GaloisField.fst Spec.AES.fst Spec.GF128.fst Spec.AES128_GCM.fst Spec.Chacha20.fst Spec.Poly1305.fst Spec.Chacha20Poly1305.fst Spec.AEAD.fst Spec.ECIES.fst tests/Spec.ECIES.Test.fst
	mkdir -p ecies-ml
	cp $(HACL_HOME)/lib/ml/Lib_RandomSequence.ml ecies-ml
	$(FSTAR) --codegen OCaml --lax $(LIBS_EX) --extract_module Spec.SHA2 --extract_module Spec.Hash --extract_module Spec.HMAC --extract_module Spec.HKDF --extract_module Spec.Curve25519 --extract_module Spec.Curve448 --extract_module Spec.DH --extract_module Spec.GaloisField --extract_module Spec.AES --extract_module Spec.GF128 --extract_module Spec.AES128_GCM --extract_module Spec.Chacha20 --extract_module Spec.Poly1305 --extract_module Spec.Chacha20Poly1305 --extract_module Spec.AEAD --extract_module Spec.ECIES --extract_module Spec.ECIES.Test --odir ecies-ml $^
	@echo 'let _ = test()' >> ecies-ml/Spec_ECIES_Test.ml
	$(OCAMLOPT) -package cryptokit -I ecies-ml $(OCAML_INCLUDES) $(addprefix ecies-ml/, $(LIBS_ML)) ecies-ml/Lib_RandomSequence.ml ecies-ml/Spec_SHA2.ml ecies-ml/Spec_Hash.ml ecies-ml/Spec_HMAC.ml ecies-ml/Spec_HKDF.ml ecies-ml/Spec_Curve25519.ml ecies-ml/Spec_Curve448.ml ecies-ml/Spec_DH.ml ecies-ml/Spec_GaloisField.ml ecies-ml/Spec_AES.ml ecies-ml/Spec_GF128.ml ecies-ml/Spec_AES128_GCM.ml ecies-ml/Spec_Chacha20.ml ecies-ml/Spec_Poly1305.ml ecies-ml/Spec_Chacha20Poly1305.ml ecies-ml/Spec_AEAD.ml ecies-ml/Spec_ECIES.ml ecies-ml/Spec_ECIES_Test.ml -o ecies.exe
	./ecies.exe

# Under CI
sha3.exe: $(LIBS_FILES) Spec.SHA3.Constants.fst Spec.SHA3.fst tests/Spec.SHA3.Test.fst
	mkdir -p sha3-ml
	$(FSTAR) --codegen OCaml --lax $(LIBS_EX) --extract_module Spec.SHA3.Constants --extract_module Spec.SHA3 --extract_module Spec.SHA3.Test --odir sha3-ml $^
	@echo 'let _ = test()' >> sha3-ml/Spec_SHA3_Test.ml
	$(OCAMLOPT) -I sha3-ml $(addprefix sha3-ml/, $(LIBS_ML)) sha3-ml/Spec_SHA3_Constants.ml sha3-ml/Spec_SHA3.ml sha3-ml/Spec_SHA3_Test.ml -o sha3.exe
	./sha3.exe

# NOT Under CI
argon2i.exe: $(LIBS_FILES) Spec.Argon2i.fst tests/Spec.Argon2i.Test.fst
	mkdir -p argon2i-ml
	$(FSTAR) --codegen OCaml --lax $(LIBS_EX) --extract_module Spec.Blake2 --extract_module Spec.Argon2i --extract_module Spec.Argon2i.Test --odir argon2i-ml $^
	@echo 'let _ = test()' >> argon2i-ml/Spec_Argon2i_Test.ml
	$(OCAMLOPT) -I argon2i-ml $(OCAML_INCLUDES) $(addprefix argon2i-ml/, $(LIBS_ML)) argon2i-ml/Spec_Blake2.ml argon2i-ml/Spec_Argon2i.ml argon2i-ml/Spec_Argon2i_Test.ml -o argon2i.exe
	./argon2i.exe

# Under CI
rsapss.exe: $(LIBS_FILES) Spec.SHA2.fst Spec.RSAPSS.fst tests/Spec.RSAPSS.Test.fst
	mkdir -p rsapss-ml
	$(FSTAR)  --codegen OCaml --lax $(LIBS_EX) --extract_module Spec.SHA2 --extract_module Spec.RSAPSS --extract_module Spec.RSAPSS.Test --odir rsapss-ml $^
	@echo 'let _ = test()' >> rsapss-ml/Spec_RSAPSS_Test.ml
	$(OCAMLOPT) -I rsapss-ml $(OCAML_INCLUDES) $(addprefix rsapss-ml/, $(LIBS_ML)) rsapss-ml/Spec_SHA2.ml rsapss-ml/Spec_RSAPSS.ml rsapss-ml/Spec_RSAPSS_Test.ml -o rsapss.exe
	./rsapss.exe

#
# NOT UNDER CI
#

# NOT Under CI
chacha20_vec.exe: $(LIBS_FILES) Spec.CTR.fst Spec.Chacha20_vec.fst tests/Spec.Chacha20_vec.Test.fst
	mkdir -p chacha20_vec-ml
	$(FSTAR) --codegen OCaml --lax $(LIBS_EX) --extract_module Spec.CTR --extract_module Spec.Chacha20_vec --extract_module Spec.Chacha20_vec.Test --odir chacha20_vec-ml $^
	@echo 'let _ = test()' >> chacha20_vec-ml/Spec_Chacha20_vec_Test.ml
	$(OCAMLOPT) -I chacha20_vec-ml chacha20_vec-ml/Lib_IntTypes.ml chacha20_vec-ml/Lib_RawIntTypes.ml chacha20_vec-ml/Lib_Sequence.ml chacha20_vec-ml/Spec_CTR.ml chacha20_vec-ml/Spec_Chacha20_vec.ml chacha20_vec-ml/Spec_Chacha20_vec_Test.ml -o chacha20_vec.exe
	./chacha20_vec.exe

# NOT Under CI
poly1305_generic.exe: $(LIBS_FILES) Spec.Poly1305.Generic.fst tests/Spec.Poly1305.Generic.Test.fst
	mkdir -p poly1305-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Lib.IntTypes --extract_module Lib.RawIntTypes --extract_module Lib.LoopCombinators --extract_module Lib.Sequence --extract_module Spec.Poly1305.Generic --extract_module Spec.Poly1305.Generic.Test --odir poly1305-ml $^
	@echo 'let _ = test()' >> poly1305-ml/Spec_Poly1305_Generic_Test.ml
	$(OCAMLOPT) -g -I poly1305-ml $(addprefix poly1305-ml/, $(LIBS_ML)) poly1305-ml/Spec_Poly1305_Generic.ml poly1305-ml/Spec_Poly1305_Generic_Test.ml -o poly1305_generic.exe
	./poly1305_generic.exe

# NOT Under CI
poly1305_ml.exe: $(LIBS_FILES) Spec.Poly1305.Generic.fst tests/Spec.Poly1305.Generic.Test.fst
	$(OCAMLOPT) -g -I poly1305-ml $(addprefix poly1305-ml/, $(LIBS_ML)) poly1305-ml/Spec_Poly1305_Generic.ml poly1305-ml/Spec_Poly1305_Generic_Test.ml -o poly1305_generic.exe
	export OCAMLRUNPARAM=b
	./poly1305_generic.exe

# NOT Under CI
qdsa.exe: $(LIBS_FILES) Spec.Curve25519.fst Spec.SHA2.fst Spec.Qdsa.fst
	$(FSTAR) --lax --codegen OCaml --include lib --include lemmas --extract_module Lib.IntTypes --extract_module Lib.LoopCombinators --extract_module Lib.Sequence --extract_module Spec.Qdsa --extract_module Spec.Curve25519 --extract_module Spec.SHA2 --extract_module Lib.RawIntTypes  --odir qdsa-ml $^
	@echo 'let _ = test()' >> qdsa-ml/Spec_Qdsa.ml
	$(OCAMLOPT) -I qdsa-ml qdsa-ml/Lib_IntTypes.ml qdsa-ml/Lib_RawIntTypes.ml qdsa-ml/Lib_Sequence.ml qdsa-ml/Spec_Curve25519.ml qdsa-ml/Spec_SHA2.ml qdsa-ml/Spec_Qdsa.ml -o qdsa.exe
	./qdsa.exe

sha2.exe: $(LIBS_FILES) Spec.SHA2.fst tests/Spec.SHA2.Test.fst
	mkdir -p sha2-ml
	$(FSTAR) --codegen OCaml --lax $(LIBS_EX) --extract_module Spec.SHA2 --extract_module Spec.SHA2.Test --odir sha2-ml $^
	@echo 'let _ = test()' >> sha2-ml/Spec_SHA2_Test.ml
	$(OCAMLOPT) -I sha2-ml $(addprefix sha2-ml/, $(LIBS_ML)) sha2-ml/Spec_SHA2.ml sha2-ml/Spec_SHA2_Test.ml -o sha2.exe
	./sha2.exe

# NOT Under CI
pbkdf2.exe: $(LIBS_FILES) Spec.SHA2.fst Spec.Hash.fst Spec.HMAC.fst Spec.PBKDF2.fst tests/Spec.PBKDF2.Test.fst
	mkdir -p pbkdf2-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Lib.IntTypes --extract_module Lib.RawIntTypes --extract_module Lib.LoopCombinators --extract_module Lib.Sequence --extract_module Lib.ByteSequence --extract_module Spec.SHA2 --extract_module Spec.Hash --extract_module Spec.HMAC --extract_module Spec.PBKDF2 --extract_module Spec.PBKDF2.Test --odir pbkdf2-ml $^
	@echo 'let _ = test()' >> pbkdf2-ml/Spec_PBKDF2_Test.ml
	$(OCAMLOPT) -I pbkdf2-ml $(OCAML_INCLUDES) pbkdf2-ml/Lib_IntTypes.ml pbkdf2-ml/Lib_RawIntTypes.ml pbkdf2-ml/Lib_Sequence.ml pbkdf2-ml/Lib_ByteSequence.ml pbkdf2-ml/Spec_SHA2.ml pbkdf2-ml/Spec_Hash.ml pbkdf2-ml/Spec_HMAC.ml pbkdf2-ml/Spec_PBKDF2.ml pbkdf2-ml/Spec_PBKDF2_Test.ml -o pbkdf2.exe
	./pbkdf2.exe

# NOT Under CI
random.exe: $(LIBS_FILES) tests/Spec.Random.Test.fst
	mkdir -p random-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Lib.IntTypes --extract_module Lib.RawIntTypes --extract_module Lib.LoopCombinators --extract_module Lib.Sequence --extract_module Lib.ByteSequence --extract_module Lib.PrintSequence --extract_module Spec.Random.Test --odir random-ml $^
	@echo 'let _ = test()' >> random-ml/Spec_Random_Test.ml
	$(OCAMLOPT) -package cryptokit -I random-ml -I ../lib/ml random-ml/Lib_IntTypes.ml random-ml/Lib_RawIntTypes.ml random-ml/Lib_LoopCombinators.ml random-ml/Lib_Sequence.ml ../lib/ml/Lib_RandomSequence.ml random-ml/Lib_ByteSequence.ml random-ml/Lib_PrintSequence.ml random-ml/Spec_Random_Test.ml -o random.exe
	./random.exe

# NOT Under CI
network.exe: $(LIBS_FILES) tests/Spec.Network.Test.fst
	mkdir -p network-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Lib.IntTypes --extract_module Lib.RawIntTypes --extract_module Lib.LoopCombinators --extract_module Lib.Sequence --extract_module Spec.Network.Test --odir network-ml $^
	@echo 'let _ = test()' >> network-ml/Spec_Network_Test.ml
	$(OCAMLOPT) -I network-ml -I ../lib/ml ../lib/ml/Lib_Network.ml network-ml/Lib_IntTypes.ml network-ml/Lib_RawIntTypes.ml network-ml/Lib_Sequence.ml network-ml/Spec_Network_Test.ml -o network.exe
	./network.exe
