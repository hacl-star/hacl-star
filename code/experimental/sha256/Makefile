HACL_HOME    ?= /opt/hacl-star
FSTAR_HOME   ?= /opt/fstar
KREMLIN_HOME ?= /opt/kremlin



extract:
	mkdir -p sha2-c
	$(KREMLIN_HOME)/krml -tmpdir sha2-c \
		-I $(HACL_HOME)/code/lib/kremlin \
		Hacl.Hash.SHA2.L256.fst Hacl.Test.Hash.SHA2.fst -o sha2.exe -no-prefix Hacl.Test.Hash.SHA2 \
		-drop 'Hacl.Cast' -drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
		-drop Prims -drop FStar Hacl.Test.Hash.SHA2.fst \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -ccopt -march=native -ccopt -std=gnu99 -verbose
	./sha2.exe


clean:
	rm -rf *~ *.exe *.exe.dSYM
	rm -rf sha2-c
