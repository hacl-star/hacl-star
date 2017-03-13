HACL_HOME    ?= /opt/hacl-star
FSTAR_HOME   ?= /opt/fstar
KREMLIN_HOME ?= /opt/kremlin

FSTAR ?= $(FSTAR_HOME)/bin/fstar.exe



verify: Hacl.Hash.SHA2.L256.fst SHA2_256.fst
	$(FSTAR) --include $(FSTAR_HOME)/ulib/hyperstack --include $(KREMLIN_HOME)/kremlib --include $(HACL_HOME)/code/lib/kremlin --include $(HACL_HOME)/code/experimental/utils --use_hints $^


build:
	mkdir -p sha2-c
	$(KREMLIN_HOME)/krml -tmpdir sha2-c \
		-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/code/experimental/utils \
		Hacl.Test.SHA2_256.fst -o sha2.exe -no-prefix Hacl.Test.SHA2_256 -no-prefix SHA2_256 \
		-drop 'Hacl.Cast' -drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
		-drop 'Hacl.Spec.Endianness' -drop 'Hacl.Endianness' -drop Prims -drop FStar Hacl.Test.SHA2_256.fst \
		-no-prefix 'Hacl.Utils.Experimental' \
		-bundle "SHA2_256=Hacl.Utils.Experimental,Hacl.Hash.SHA2.L256,SHA2_256" \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -ccopt -Wno-error=strict-aliasing -ccopt -march=native -ccopt -std=gnu99 $(VERBOSE)
	./sha2.exe


extract-c:
	mkdir -p sha2-c
	$(KREMLIN_HOME)/krml -tmpdir sha2-c \
		-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/code/experimental/utils \
		Hacl.Test.SHA2_256.fst -o sha2.exe -no-prefix Hacl.Test.SHA2_256 -no-prefix SHA2_256 \
		-drop 'Hacl.Cast' -drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
		-drop 'Hacl.Spec.Endianness' -drop 'Hacl.Endianness' -drop Prims -drop FStar Hacl.Test.SHA2_256.fst \
		-no-prefix 'Hacl.Utils.Experimental' -no-prefix 'Hacl.Hash.SHA2.L256' -no-prefix 'SHA2_256' \
		-bundle "SHA2_256=Hacl.Utils.Experimental,Hacl.Hash.SHA2.L256,SHA2_256" \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -ccopt -Wno-error=strict-aliasing -ccopt -march=native -ccopt -std=gnu99 -skip-compilation $(VERBOSE)


clean:
	rm -rf *~ *.exe *.exe.dSYM
	rm -rf sha2-c
