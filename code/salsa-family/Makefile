FSTAR_HOME?=../../../FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
HACL_HOME?=../..
include ../Makefile.include


SALSA_FILES= \
	Hacl.Symmetric.Salsa20.fst \
	Hacl.Symmetric.HSalsa20.fst \
	Hacl.Symmetric.XSalsa20.fst \
	Hacl.Symmetric.Chacha20.fst \
	Hacl.Test.Salsa20.fst \
	Hacl.Test.XSalsa20.fst \
	Hacl.Test.Chacha20.fst 

SALSA_MODULES= $(basename $(SALSA_FILES))


%.fst-verify: %.fst
	$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib $^ 

verify: $(addsuffix -verify, $(SALSA_FILES))


extract-c:
	mkdir -p salsa-c
	$(KREMLIN_HOME)/krml -I $(FSTAR_HOME)/ulib/hyperstack -tmpdir salsa-c -verbose \
		-I ../bignum -I ../lib/kremlin -I $(FSTAR_HOME)/../kremlin/kremlib -I $(FSTAR_HOME)/../kremlin/test \
		$(SALSA_FILES) \
		-drop FStar -drop Prims -drop Hacl.Cast -drop Hacl.UInt8 -drop Hacl.UInt32 -drop Hacl.UInt64 \
		-drop Hacl.UInt128 -bundle Hacl.Spec \
		$(FSTAR_HOME)/../kremlin/test/testlib.c -add-include '"testlib.h"' \
		-ccopt -Wno-error=pointer-sign -ccopt -Wno-error=incompatible-pointer-types \
                -ccopt -Wno-error=format= -no-prefix Hacl.Test.Poly1305_64 -ccopt -flto -ccopt -march=native -ccopt -c


clean:
	rm -rf *.exe *.exe.* *.out *~ poly1305-c
