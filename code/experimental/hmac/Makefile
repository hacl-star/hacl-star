HACL_HOME    ?= /opt/hacl-star
FSTAR_HOME   ?= /opt/fstar
KREMLIN_HOME ?= /opt/kremlin



build:
	mkdir -p hmac-c
	$(KREMLIN_HOME)/krml -tmpdir hmac-c \
		-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/code/experimental/utils -I $(HACL_HOME)/code/experimental/hash \
		Hacl.HMAC.fst Hacl.Test.HMAC.fst -o hmac.exe -no-prefix Hacl.Test.HMAC \
		-drop 'Hacl.Cast' -drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
		-drop 'Hacl.Spec.Endianness' -drop Prims -drop FStar Hacl.Test.Hash.SHA2.fst \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -ccopt -Wno-error=strict-aliasing -ccopt -march=native -ccopt -std=gnu99 -verbose
	./hmac.exe


extract-c:
	mkdir -p hmac-c
	$(KREMLIN_HOME)/krml -tmpdir hmac-c \
		-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/code/experimental/utils  -I $(HACL_HOME)/code/experimental/sha256 \
		-no-prefix Hacl.HMAC -skip-compilation \
		-drop 'Hacl.Cast' -drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
		-drop Prims -drop FStar Hacl.HMAC.fst -verbose

clean:
	rm -rf *~ *.exe *.exe.dSYM
	rm -rf hmac-c
