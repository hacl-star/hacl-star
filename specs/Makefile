include ../Makefile.include

.PHONY=all test

FSTAR_INCLUDES+=--include $(HACL_HOME)/specs/lib --include $(HACL_HOME)/specs/lib/fst --include $(HACL_HOME)/specs/lemmas --expose_interfaces

SPEC_FILES=	Spec.Chacha20.fst \
		Spec.Poly1305.fst \
		Spec.CTR.fst \
		Spec.Chacha20Poly1305.fst \
		Spec.Curve25519.fst \
		Spec.Curve448.fst \
		Spec.Salsa20.fst \
		Spec.SHA2.fst \
		Spec.Ed25519.fst \
		Spec.Chacha20_vec.fst \
		Spec.GaloisField.fst \
		Spec.GF128.fst \
		Spec.HMAC.fst \
		Spec.HSalsa20.fst 

hints: $(addsuffix .hints, $(SPEC_FILES))
verify: $(addsuffix -verify, $(SPEC_FILES))
all-hints: hints
all-ver: verify

all: test
test: chacha20.exe salsa20.exe poly1305.exe chacha20poly1305.exe curve25519.exe curve448.exe qdsa.exe sha2.exe ed25519.exe hmac.exe hkdf.exe 


noise.exe: lib/fst/Spec.Lib.IntTypes.fst lib/fst/Spec.Lib.RawIntTypes.fst lib/fst/Spec.Lib.IntSeq.fst Spec.Noise.fst
	mkdir -p noise-ml
	$(FSTAR) --expose_interfaces --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes  --extract_module Spec.Lib.IntSeq --extract_module Spec.Noise --odir noise-ml $^
	@echo 'let _ = test()' >> noise-ml/Spec_Noise.ml
	$(OCAMLOPT) -I noise-ml noise-ml/Spec_Lib_IntTypes.ml noise-ml/Spec_Lib_RawIntTypes.ml noise-ml/Spec_Lib_IntSeq.ml noise-ml/Spec_Noise.ml -o noise.exe
	./noise.exe

chacha20.exe: lib/fst/Spec.Lib.IntTypes.fst lib/fst/Spec.Lib.RawIntTypes.fst lib/fst/Spec.Lib.IntSeq.fst Spec.CTR.fst Spec.Chacha20.fst tests/Spec.Chacha20.Test.fst
	mkdir -p chacha20-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes  --extract_module Spec.Lib.IntSeq  --extract_module Spec.CTR --extract_module Spec.Chacha20 --extract_module Spec.Chacha20.Test --odir chacha20-ml $^
	@echo 'let _ = test()' >> chacha20-ml/Spec_Chacha20_Test.ml
	$(OCAMLOPT) -I chacha20-ml chacha20-ml/Spec_Lib_IntTypes.ml chacha20-ml/Spec_Lib_RawIntTypes.ml chacha20-ml/Spec_Lib_IntSeq.ml chacha20-ml/Spec_CTR.ml chacha20-ml/Spec_Chacha20.ml chacha20-ml/Spec_Chacha20_Test.ml -o chacha20.exe
	./chacha20.exe

chacha20_vec.exe: lib/fst/Spec.Lib.IntTypes.fst lib/fst/Spec.Lib.RawIntTypes.fst lib/fst/Spec.Lib.IntSeq.fst Spec.CTR.fst Spec.Chacha20_vec.fst tests/Spec.Chacha20_vec.Test.fst
	mkdir -p chacha20_vec-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes  --extract_module Spec.Lib.IntSeq  --extract_module Spec.CTR --extract_module Spec.Chacha20_vec --extract_module Spec.Chacha20_vec.Test --odir chacha20_vec-ml $^
	@echo 'let _ = test()' >> chacha20_vec-ml/Spec_Chacha20_vec_Test.ml
	$(OCAMLOPT) -I chacha20_vec-ml chacha20_vec-ml/Spec_Lib_IntTypes.ml chacha20_vec-ml/Spec_Lib_RawIntTypes.ml chacha20_vec-ml/Spec_Lib_IntSeq.ml chacha20_vec-ml/Spec_CTR.ml chacha20_vec-ml/Spec_Chacha20_vec.ml chacha20_vec-ml/Spec_Chacha20_vec_Test.ml -o chacha20_vec.exe
	./chacha20_vec.exe

salsa20.exe: lib/fst/Spec.Lib.IntTypes.fst lib/fst/Spec.Lib.RawIntTypes.fst lib/fst/Spec.Lib.IntSeq.fst Spec.CTR.fst Spec.Salsa20.fst tests/Spec.Salsa20.Test.fst
	mkdir -p salsa20-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes  --extract_module Spec.Lib.IntSeq  --extract_module Spec.CTR --extract_module Spec.Salsa20 --extract_module Spec.Salsa20.Test --odir salsa20-ml $^
	@echo 'let _ = test()' >> salsa20-ml/Spec_Salsa20_Test.ml
	$(OCAMLOPT) -I salsa20-ml salsa20-ml/Spec_Lib_IntTypes.ml salsa20-ml/Spec_Lib_RawIntTypes.ml salsa20-ml/Spec_Lib_IntSeq.ml salsa20-ml/Spec_CTR.ml salsa20-ml/Spec_Salsa20.ml salsa20-ml/Spec_Salsa20_Test.ml -o salsa20.exe
	./salsa20.exe

poly1305.exe: lib/fst/Spec.Lib.IntTypes.fst lib/fst/Spec.Lib.RawIntTypes.fst lib/fst/Spec.Lib.IntSeq.fst Spec.Poly1305.fst tests/Spec.Poly1305.Test.fst
	mkdir -p poly1305-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes --extract_module Spec.Lib.IntSeq --extract_module Spec.Poly1305 --extract_module Spec.Poly1305.Test --odir poly1305-ml $^
	@echo 'let _ = test()' >> poly1305-ml/Spec_Poly1305_Test.ml
	$(OCAMLOPT) -I poly1305-ml poly1305-ml/Spec_Lib_IntTypes.ml poly1305-ml/Spec_Lib_IntSeq.ml poly1305-ml/Spec_Poly1305.ml poly1305-ml/Spec_Poly1305_Test.ml -o poly1305.exe
	./poly1305.exe

chacha20poly1305.exe: lib/fst/Spec.Lib.IntTypes.fst lib/fst/Spec.Lib.RawIntTypes.fst lib/fst/Spec.Lib.IntSeq.fst Spec.CTR.fst Spec.Chacha20.fst Spec.Poly1305.fst Spec.Chacha20Poly1305.fst tests/Spec.Chacha20Poly1305.Test.fst
	mkdir -p chacha20poly1305-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes --extract_module Spec.Lib.IntSeq --extract_module Spec.CTR --extract_module Spec.Chacha20 --extract_module Spec.Poly1305 --extract_module Spec.Chacha20Poly1305 --extract_module Spec.Chacha20Poly1305.Test --odir chacha20poly1305-ml $^
	@echo 'let _ = test()' >> chacha20poly1305-ml/Spec_Chacha20Poly1305_Test.ml
	$(OCAMLOPT) -I chacha20poly1305-ml chacha20poly1305-ml/Spec_Lib_IntTypes.ml chacha20poly1305-ml/Spec_Lib_IntSeq.ml chacha20poly1305-ml/Spec_CTR.ml chacha20poly1305-ml/Spec_Chacha20.ml chacha20poly1305-ml/Spec_Poly1305.ml chacha20poly1305-ml/Spec_Chacha20Poly1305.ml chacha20poly1305-ml/Spec_Chacha20Poly1305_Test.ml -o chacha20poly1305.exe
	./chacha20poly1305.exe

gf128.exe: lib/fst/Spec.Lib.IntTypes.fst lib/fst/Spec.Lib.RawIntTypes.fst lib/fst/Spec.Lib.IntSeq.fst Spec.GaloisField.fst Spec.GF128.fst tests/Spec.GF128.Test.fst
	mkdir -p gf128-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes --extract_module Spec.Lib.IntSeq --extract_module Spec.GaloisField --extract_module Spec.GF128 --extract_module Spec.GF128.Test --odir gf128-ml $^
	@echo 'let _ = test()' >> gf128-ml/Spec_GF128_Test.ml
	$(OCAMLOPT) -I gf128-ml $(OCAML_INCLUDES) gf128-ml/Spec_Lib_IntTypes.ml gf128-ml/Spec_Lib_IntSeq.ml gf128-ml/Spec_GaloisField.ml gf128-ml/Spec_GF128.ml gf128-ml/Spec_GF128_Test.ml -o gf128.exe
	./gf128.exe

sbox.exe: lib/fst/Spec.Lib.IntTypes.fst lib/fst/Spec.Lib.RawIntTypes.fst lib/fst/Spec.Lib.IntSeq.fst Spec.GaloisField.fst Spec.Sbox.fst
	mkdir -p sbox-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes --extract_module Spec.Lib.IntSeq --extract_module FStar.BitVector --extract_module Spec.GaloisField --extract_module Spec.Sbox --odir sbox-ml $^
	@echo 'let _ = test()' >> sbox-ml/Spec_Sbox.ml
	$(OCAMLOPT) -I sbox-ml $(OCAML_INCLUDES) sbox-ml/Spec_Lib_IntTypes.ml sbox-ml/Spec_Lib_IntSeq.ml sbox-ml/Spec_GaloisField.ml sbox-ml/Spec_Sbox.ml -o sbox.exe
	./sbox.exe


aes.exe: lib/fst/Spec.Lib.IntTypes.fst lib/fst/Spec.Lib.RawIntTypes.fst lib/fst/Spec.Lib.IntSeq.fst Spec.GaloisField.fst Spec.CTR.fst Spec.AES.fst tests/Spec.AES.Test.fst
	mkdir -p aes-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes --extract_module Spec.Lib.IntSeq --extract_module Spec.GaloisField --extract_module Spec.CTR --extract_module Spec.AES --extract_module Spec.AES.Test --odir aes-ml $^
	@echo 'let _ = test()' >> aes-ml/Spec_AES_Test.ml
	$(OCAMLOPT) -I aes-ml $(OCAML_INCLUDES) aes-ml/Spec_Lib_IntTypes.ml aes-ml/Spec_Lib_IntSeq.ml aes-ml/Spec_GaloisField.ml aes-ml/Spec_CTR.ml aes-ml/Spec_AES.ml aes-ml/Spec_AES_Test.ml -o aes.exe
	./aes.exe

aesgcm.exe: lib/fst/Spec.Lib.IntTypes.fst lib/fst/Spec.Lib.RawIntTypes.fst lib/fst/Spec.Lib.IntSeq.fst Spec.GaloisField.fst Spec.CTR.fst Spec.AES.fst Spec.GF128.fst Spec.AESGCM.fst tests/Spec.AESGCM.Test.fst
	mkdir -p aesgcm-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes --extract_module Spec.Lib.IntSeq --extract_module Spec.GaloisField --extract_module Spec.CTR --extract_module Spec.AES --extract_module Spec.AESGCM  --extract_module Spec.AESGCM.Test --extract_module Spec.GF128 --odir aesgcm-ml $^
	@echo 'let _ = test()' >> aesgcm-ml/Spec_AESGCM_Test.ml
	$(OCAMLOPT) -I aesgcm-ml $(OCAML_INCLUDES) aesgcm-ml/Spec_Lib_IntTypes.ml aesgcm-ml/Spec_Lib_IntSeq.ml aesgcm-ml/Spec_GaloisField.ml aesgcm-ml/Spec_CTR.ml aesgcm-ml/Spec_AES.ml aesgcm-ml/Spec_GF128.ml aesgcm-ml/Spec_AESGCM.ml aesgcm-ml/Spec_AESGCM_Test.ml -o aesgcm.exe
	./aesgcm.exe

curve25519.exe: lib/fst/Spec.Lib.IntTypes.fst lib/fst/Spec.Lib.RawIntTypes.fst lib/fst/Spec.Lib.IntSeq.fst Spec.Curve25519.fst tests/Spec.Curve25519.Test.fst
	mkdir -p curve25519-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes --extract_module Spec.Lib.IntSeq --extract_module Spec.Curve25519 --extract_module Spec.Curve25519.Test --odir curve25519-ml $^
	@echo 'let _ = test()' >> curve25519-ml/Spec_Curve25519_Test.ml
	$(OCAMLOPT) -I curve25519-ml curve25519-ml/Spec_Lib_IntTypes.ml curve25519-ml/Spec_Lib_IntSeq.ml curve25519-ml/Spec_Curve25519.ml curve25519-ml/Spec_Curve25519_Test.ml -o curve25519.exe
	./curve25519.exe


kyber.exe: lib/fst/Spec.Lib.IntTypes.fst lib/fst/Spec.Lib.RawIntTypes.fst lib/fst/Spec.Lib.IntSeq.fst Spec.Kyber.fst 
	mkdir -p kyber-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes --extract_module Spec.Lib.IntSeq --extract_module Spec.Kyber --odir kyber-ml $^
	@echo 'let _ = test()' >> kyber-ml/Spec_Kyber.ml
	$(OCAMLOPT) -I kyber-ml kyber-ml/Spec_Lib_IntTypes.ml kyber-ml/Spec_Lib_IntSeq.ml kyber-ml/Spec_Kyber.ml -o kyber.exe
	./kyber.exe

curve448.exe: lib/fst/Spec.Lib.IntTypes.fst lib/fst/Spec.Lib.RawIntTypes.fst lib/fst/Spec.Lib.IntSeq.fst Spec.Curve448.fst tests/Spec.Curve448.Test.fst
	mkdir -p curve448-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes --extract_module Spec.Lib.IntSeq --extract_module Spec.Curve448 --extract_module Spec.Curve448.Test --odir curve448-ml $^
	@echo 'let _ = test()' >> curve448-ml/Spec_Curve448_Test.ml
	$(OCAMLOPT) -I curve448-ml curve448-ml/Spec_Lib_IntTypes.ml curve448-ml/Spec_Lib_IntSeq.ml curve448-ml/Spec_Curve448.ml curve448-ml/Spec_Curve448_Test.ml -o curve448.exe
	./curve448.exe

qdsa.exe: lib/fst/Spec.Lib.IntTypes.fst lib/fst/Spec.Lib.RawIntTypes.fst lib/fst/Spec.Lib.IntSeq.fst Spec.Curve25519.fst Spec.SHA2.fst Spec.Qdsa.fst
	$(FSTAR) --lax --codegen OCaml --include lib --include lemmas --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.IntSeq --extract_module Spec.Qdsa --extract_module Spec.Curve25519 --extract_module Spec.SHA2 --extract_module Spec.Lib.RawIntTypes  --odir qdsa-ml $^
	@echo 'let _ = test()' >> qdsa-ml/Spec_Qdsa.ml
	$(OCAMLOPT) -I qdsa-ml qdsa-ml/Spec_Lib_IntTypes.ml qdsa-ml/Spec_Lib_RawIntTypes.ml qdsa-ml/Spec_Lib_IntSeq.ml qdsa-ml/Spec_Curve25519.ml qdsa-ml/Spec_SHA2.ml qdsa-ml/Spec_Qdsa.ml -o qdsa.exe
	./qdsa.exe

sha2.exe: lib/fst/Spec.Lib.IntTypes.fst lib/fst/Spec.Lib.RawIntTypes.fst lib/fst/Spec.Lib.IntSeq.fst lib/fst/Spec.Lib.Stateful.fst Spec.SHA2.fst tests/Spec.SHA2.Test.fst
	mkdir -p sha2-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes --extract_module Spec.Lib.IntSeq --extract_module Spec.Lib.Stateful --extract_module Spec.SHA2 --extract_module Spec.SHA2.Test --odir sha2-ml $^
	@echo 'let _ = test()' >> sha2-ml/Spec_SHA2_Test.ml
	$(OCAMLOPT) -I sha2-ml sha2-ml/Spec_Lib_IntTypes.ml sha2-ml/Spec_Lib_RawIntTypes.ml sha2-ml/Spec_Lib_IntSeq.ml sha2-ml/Spec_Lib_Stateful.ml sha2-ml/Spec_SHA2.ml sha2-ml/Spec_SHA2_Test.ml -o sha2.exe
	./sha2.exe

keccak.exe: lib/fst/Spec.Lib.IntTypes.fst lib/fst/Spec.Lib.RawIntTypes.fst lib/fst/Spec.Lib.IntSeq.fst lib/fst/Spec.Lib.Stateful.fst Spec.Keccak.fst tests/Spec.Keccak.Test.fst
	mkdir -p keccak-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes --extract_module Spec.Lib.IntSeq --extract_module Spec.Lib.Stateful --extract_module Spec.Keccak --extract_module Spec.Keccak.Test --odir keccak-ml $^
	@echo 'let _ = test()' >> keccak-ml/Spec_Keccak_Test.ml
	$(OCAMLOPT) -I keccak-ml keccak-ml/Spec_Lib_IntTypes.ml keccak-ml/Spec_Lib_RawIntTypes.ml keccak-ml/Spec_Lib_IntSeq.ml keccak-ml/Spec_Lib_Stateful.ml keccak-ml/Spec_Keccak.ml keccak-ml/Spec_Keccak_Test.ml -o keccak.exe
	./keccak.exe

blake2s.exe: lib/fst/Spec.Lib.IntTypes.fst lib/fst/Spec.Lib.RawIntTypes.fst lib/fst/Spec.Lib.IntSeq.fst lib/fst/Spec.Lib.Stateful.fst Spec.Blake2s.fst tests/Spec.Blake2s.Test.fst
	mkdir -p blake2s-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes --extract_module Spec.Lib.IntSeq --extract_module Spec.Lib.Stateful --extract_module Spec.Blake2s --extract_module Spec.Blake2s.Test --odir blake2s-ml $^
	@echo 'let _ = test()' >> blake2s-ml/Spec_Blake2s_Test.ml
	$(OCAMLOPT) -I blake2s-ml blake2s-ml/Spec_Lib_IntTypes.ml blake2s-ml/Spec_Lib_RawIntTypes.ml blake2s-ml/Spec_Lib_IntSeq.ml blake2s-ml/Spec_Lib_Stateful.ml blake2s-ml/Spec_Blake2s.ml blake2s-ml/Spec_Blake2s_Test.ml -o blake2s.exe
	./blake2s.exe

blake2b.exe: lib/fst/Spec.Lib.IntTypes.fst lib/fst/Spec.Lib.RawIntTypes.fst lib/fst/Spec.Lib.IntSeq.fst lib/fst/Spec.Lib.Stateful.fst Spec.Blake2b.fst tests/Spec.Blake2b.Test.fst
	mkdir -p blake2b-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes --extract_module Spec.Lib.IntSeq --extract_module Spec.Lib.Stateful --extract_module Spec.Blake2b --extract_module Spec.Blake2b.Test --odir blake2b-ml $^
	@echo 'let _ = test()' >> blake2b-ml/Spec_Blake2b_Test.ml
	$(OCAMLOPT) -I blake2b-ml blake2b-ml/Spec_Lib_IntTypes.ml blake2b-ml/Spec_Lib_RawIntTypes.ml blake2b-ml/Spec_Lib_IntSeq.ml blake2b-ml/Spec_Lib_Stateful.ml blake2b-ml/Spec_Blake2b.ml blake2b-ml/Spec_Blake2b_Test.ml -o blake2b.exe
	./blake2b.exe

argon2i.exe: lib/fst/Spec.Lib.IntTypes.fst lib/fst/Spec.Lib.RawIntTypes.fst lib/fst/Spec.Lib.IntSeq.fst lib/fst/Spec.Lib.Stateful.fst Spec.Argon2i.fst tests/Spec.Argon2i.Test.fst
	mkdir -p argon2i-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes --extract_module Spec.Lib.IntSeq --extract_module Spec.Lib.Stateful --extract_module Spec.Blake2b --extract_module Spec.Argon2i --extract_module Spec.Argon2i.Test --odir argon2i-ml $^
	@echo 'let _ = test()' >> argon2i-ml/Spec_Argon2i_Test.ml
	$(OCAMLOPT) -I argon2i-ml argon2i-ml/Spec_Lib_IntTypes.ml argon2i-ml/Spec_Lib_RawIntTypes.ml argon2i-ml/Spec_Lib_IntSeq.ml argon2i-ml/Spec_Lib_Stateful.ml argon2i-ml/Spec_Blake2b.ml argon2i-ml/Spec_Argon2i.ml argon2i-ml/Spec_Argon2i_Test.ml -o argon2i.exe
	./argon2i.exe


hmac.exe: lib/fst/Spec.Lib.IntTypes.fst lib/fst/Spec.Lib.RawIntTypes.fst lib/fst/Spec.Lib.IntSeq.fst lib/fst/Spec.Lib.Stateful.fst Spec.SHA2.fst Spec.Hash.fst Spec.HMAC.fst tests/Spec.HMAC.Test.fst
	mkdir -p hmac-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes --extract_module Spec.Lib.IntSeq --extract_module Spec.Lib.Stateful --extract_module Spec.SHA2 --extract_module Spec.Hash --extract_module Spec.HMAC --extract_module Spec.HMAC.Test --odir hmac-ml $^
	@echo 'let _ = test()' >> hmac-ml/Spec_HMAC_Test.ml
	$(OCAMLOPT) -I hmac-ml hmac-ml/Spec_Lib_IntTypes.ml hmac-ml/Spec_Lib_RawIntTypes.ml hmac-ml/Spec_Lib_IntSeq.ml hmac-ml/Spec_Lib_Stateful.ml hmac-ml/Spec_SHA2.ml hmac-ml/Spec_Hash.ml hmac-ml/Spec_HMAC.ml hmac-ml/Spec_HMAC_Test.ml -o hmac.exe
	./hmac.exe

hkdf.exe: lib/fst/Spec.Lib.IntTypes.fst lib/fst/Spec.Lib.RawIntTypes.fst lib/fst/Spec.Lib.IntSeq.fst lib/fst/Spec.Lib.Stateful.fst Spec.SHA2.fst Spec.Hash.fst Spec.HMAC.fst Spec.HKDF.fst tests/Spec.HKDF.Test.fst
	mkdir -p hkdf-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes --extract_module Spec.Lib.IntSeq --extract_module Spec.Lib.Stateful --extract_module Spec.SHA2 --extract_module Spec.Hash --extract_module Spec.HMAC --extract_module Spec.HKDF --extract_module Spec.HKDF.Test --odir hkdf-ml $^
	@echo 'let _ = test()' >> hkdf-ml/Spec_HKDF_Test.ml
	$(OCAMLOPT) -I hkdf-ml hkdf-ml/Spec_Lib_IntTypes.ml hkdf-ml/Spec_Lib_RawIntTypes.ml hkdf-ml/Spec_Lib_IntSeq.ml hkdf-ml/Spec_Lib_Stateful.ml hkdf-ml/Spec_SHA2.ml hkdf-ml/Spec_Hash.ml hkdf-ml/Spec_HMAC.ml hkdf-ml/Spec_HKDF.ml hkdf-ml/Spec_HKDF_Test.ml -o hkdf.exe
	./hkdf.exe

pbkdf2.exe: lib/fst/Spec.Lib.IntTypes.fst lib/fst/Spec.Lib.RawIntTypes.fst lib/fst/Spec.Lib.IntSeq.fst lib/fst/Spec.Lib.Stateful.fst Spec.SHA2.fst Spec.Hash.fst Spec.HMAC.fst Spec.PBKDF2.fst tests/Spec.PBKDF2.Test.fst
	mkdir -p pbkdf2-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes --extract_module Spec.Lib.IntSeq --extract_module Spec.Lib.Stateful --extract_module Spec.SHA2 --extract_module Spec.Hash --extract_module Spec.HMAC --extract_module Spec.PBKDF2 --extract_module Spec.PBKDF2.Test --odir pbkdf2-ml $^
	@echo 'let _ = test()' >> pbkdf2-ml/Spec_PBKDF2_Test.ml
	$(OCAMLOPT) -I pbkdf2-ml $(OCAML_INCLUDES) pbkdf2-ml/Spec_Lib_IntTypes.ml pbkdf2-ml/Spec_Lib_RawIntTypes.ml pbkdf2-ml/Spec_Lib_IntSeq.ml pbkdf2-ml/Spec_Lib_Stateful.ml pbkdf2-ml/Spec_SHA2.ml pbkdf2-ml/Spec_Hash.ml pbkdf2-ml/Spec_HMAC.ml pbkdf2-ml/Spec_PBKDF2.ml pbkdf2-ml/Spec_PBKDF2_Test.ml -o pbkdf2.exe
	./pbkdf2.exe

ed25519.exe: lib/fst/Spec.Lib.IntTypes.fst lib/fst/Spec.Lib.RawIntTypes.fst lib/fst/Spec.Lib.IntSeq.fst lib/fst/Spec.Lib.Stateful.fst Spec.SHA2.fst Spec.Curve25519.fst Spec.Ed25519.fst tests/Spec.Ed25519.Test.fst
	mkdir -p ed25519-ml
	$(FSTAR) --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes --extract_module Spec.Lib.IntSeq --extract_module Spec.Lib.Stateful --extract_module Spec.SHA2 --extract_module Spec.Curve25519 --extract_module Spec.Ed25519 --extract_module Spec.Ed25519.Test --odir ed25519-ml $^
	@echo 'let _ = test()' >> ed25519-ml/Spec_Ed25519_Test.ml
	$(OCAMLOPT) -I ed25519-ml ed25519-ml/Spec_Lib_IntTypes.ml ed25519-ml/Spec_Lib_RawIntTypes.ml ed25519-ml/Spec_Lib_IntSeq.ml ed25519-ml/Spec_Lib_Stateful.ml ed25519-ml/Spec_SHA2.ml ed25519-ml/Spec_Curve25519.ml ed25519-ml/Spec_Ed25519.ml ed25519-ml/Spec_Ed25519_Test.ml -o ed25519.exe
	./ed25519.exe

network.exe: lib/fst/Spec.Lib.IntTypes.fst lib/fst/Spec.Lib.RawIntTypes.fst lib/fst/Spec.Lib.IntSeq.fst tests/Spec.Network.Test.fst
	mkdir -p network-ml
	$(FSTAR) --include lib --codegen OCaml --lax --extract_module Spec.Lib.IntTypes --extract_module Spec.Lib.RawIntTypes --extract_module Spec.Lib.IntSeq --extract_module Spec.Network.Test --odir network-ml $^
	@echo 'let _ = test()' >> network-ml/Spec_Network_Test.ml
	$(OCAMLOPT) -I network-ml -I lib/ml lib/ml/Spec_Lib_IO_Tcp.ml network-ml/Spec_Lib_IntTypes.ml network-ml/Spec_Lib_RawIntTypes.ml network-ml/Spec_Lib_IntSeq.ml network-ml/Spec_Network_Test.ml -o network.exe
	./network.exe

clean:
	$(MAKE) -C ../code/lib/ml clean
	rm -rf *.cmi *.cmo *.cmx *.o *~ *.out *.exe *-ml
