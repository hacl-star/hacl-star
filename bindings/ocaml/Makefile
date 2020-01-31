all:
	OCAMLPATH=$(HACL_HOME)/dist/gcc-compatible/ ocamlbuild -use-ocamlfind -package ocamlevercrypt,bigstring -I tests aead_test.native curve25519_test.native ed25519_test.native hash_test.native poly1305_test.native hmac_test.native hkdf_test.native nacl_test.native
	LD_LIBRARY_PATH=. ./aead_test.native
	LD_LIBRARY_PATH=. ./curve25519_test.native
	LD_LIBRARY_PATH=. ./ed25519_test.native
	LD_LIBRARY_PATH=. ./hash_test.native
	LD_LIBRARY_PATH=. ./poly1305_test.native
	LD_LIBRARY_PATH=. ./hmac_test.native
	LD_LIBRARY_PATH=. ./hkdf_test.native
	LD_LIBRARY_PATH=. ./nacl_test.native

# VD: as far as I understand this shouldn't be necessary but I wasn't able to make ocamlfind see the ocamlevercrypt package
# without installing it globally
install-ocamlevercrypt:
	cd $(HACL_HOME)/dist/gcc-compatible && ocamlfind install ocamlevercrypt META *\.* lib/* lib_gen/*

clean:
	rm -rf _build *.native
