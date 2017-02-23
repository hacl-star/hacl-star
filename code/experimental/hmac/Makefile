HACL_HOME    ?= /opt/hacl-star
FSTAR_HOME   ?= /opt/fstar
KREMLIN_HOME ?= /opt/kremlin

FSTAR ?= $(FSTAR_HOME)/bin/fstar.exe



verify:
	$(FSTAR) --include $(FSTAR_HOME)/ulib/hyperstack --include $(KREMLIN_HOME)/kremlib --include $(HACL_HOME)/code/lib --include $(HACL_HOME)/code/experimental/utils --include $(HACL_HOME)/code/experimental/hash HMAC_SHA2_256.fst --use_hints


build:
	mkdir -p hmac-c
	$(KREMLIN_HOME)/krml -tmpdir hmac-c \
		-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/code/experimental/utils -I $(HACL_HOME)/code/experimental/hash \
		Hacl.Test.HMAC.SHA2.L256.fst -o hmac.exe -no-prefix Hacl.Test.HMAC.SHA2.L256 \
		-drop 'Hacl.Cast' -drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
		-drop 'Hacl.Spec.Endianness' -drop 'Hacl.Endianness' -drop Prims -drop FStar \
		-bundle "HMAC_SHA2_256=Hacl.Utils.Experimental,Hacl.Hash.SHA2.L256,Hacl.HMAC.SHA2.L256,HMAC.SHA2.L256" \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -ccopt -Wno-error=strict-aliasing -ccopt -march=native -ccopt -std=gnu99 -verbose
	./hmac.exe


extract-c:
	mkdir -p hmac-c
	$(KREMLIN_HOME)/krml -tmpdir hmac-c \
		-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/code/experimental/utils -I $(HACL_HOME)/code/experimental/hash \
		Hacl.Test.HMAC.SHA2.L256.fst -o hmac.exe -no-prefix Hacl.Test.HMAC.SHA2.L256 \
		-drop 'Hacl.Cast' -drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
		-drop 'Hacl.Spec.Endianness' -drop 'Hacl.Endianness' -drop Prims -drop FStar \
		-bundle "HMAC_SHA2_256=Hacl.Utils.Experimental,Hacl.Hash.SHA2.L256,Hacl.HMAC.SHA2.L256,HMAC.SHA2.L256" \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -ccopt -Wno-error=strict-aliasing -ccopt -march=native -ccopt -std=gnu99 -skip-compilation -verbose


clean:
	rm -rf *~ *.exe *.exe.dSYM
	rm -rf hmac-c
