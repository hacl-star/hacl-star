# all:
# 	OCAMLPATH=$(HACL_HOME)/dist/gcc-compatible ocamlbuild -use-ocamlfind ocamlopt -I . -I lib -I lib_gen -package hacl,ctypes,ctypes.foreign,bigstring -cclib -Wl,-E -ccopt -L. -cclib -levercrypt ocamlevercrypt.cmxa EverCryptHigh.mli EverCryptHigh.ml aead_test.ml -o aead_test.native

all:
	OCAMLPATH=$(HACL_HOME)/dist/gcc-compatible/ ocamlbuild -use-ocamlfind -package ocamlevercrypt,bigstring aead_test.native
	LD_LIBRARY_PATH=. ./aead_test.native

# VD: as far as I understand this shouldn't be necessary but I wasn't able to make ocamlfind see the ocamlevercrypt package
# without installing it globally
install-ocamlevercrypt:
	cd $(HACL_HOME)/dist/gcc-compatible && ocamlfind install ocamlevercrypt META *\.* lib/* lib_gen/*

clean:
	rm -rf _build *.native
