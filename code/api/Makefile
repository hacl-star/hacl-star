FSTAR_HOME?=../../../FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
HACL_HOME?=../..
include ../Makefile.include

API_FILES= \
	Hacl.Constants.fst \
	Hacl.SecretBox.fst \
	Hacl.Box.fst

%.fst-verify: %.fst
	$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib --include ../bignum $^ --use_hints

verify: $(addsuffix -verify, $(API_FILES))

extract-c:
	mkdir -p api-c
	$(KREMLIN_HOME)/krml -I $(FSTAR_HOME)/ulib/hyperstack -tmpdir api-c -verbose \
		-I ../bignum -I ../lib/kremlin -I $(FSTAR_HOME)/../kremlin/kremlib -I $(FSTAR_HOME)/../kremlin/test \
		-I ../salsa-family -I ../poly1305/interfaces -I ../curve25519/interfaces $(API_FILES) \
		-drop FStar -drop Hacl.Spec -drop Prims -drop Hacl.Cast -drop Hacl.UInt8 -drop Hacl.UInt32 -drop Hacl.UInt64 \
		-drop Hacl.UInt128  -drop Hacl.Bignum.Constants -drop Hacl.Bignum.Parameters -drop Hacl.Bignum.Limb -drop Hacl.Bignum.Wide \
		-bundle Hacl.Spec \
		$(FSTAR_HOME)/../kremlin/test/testlib.c -add-include '"testlib.h"' \
		-ccopt -Wno-error=pointer-sign -ccopt -Wno-error=incompatible-pointer-types \
                -ccopt -Wno-error=format= -no-prefix Hacl.Test.Poly1305_64 -ccopt -flto -ccopt -march=native -o poly1305.exe
