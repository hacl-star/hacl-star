HACL_HOME    ?= /opt/hacl-star
FSTAR_HOME   ?= /opt/fstar
KREMLIN_HOME ?= /opt/kremlin

FSTAR ?= $(FSTAR_HOME)/bin/fstar.exe



verify: Hacl.Hash.SHA2.L256.fst
	$(FSTAR) --include $(FSTAR_HOME)/ulib/hyperstack --include $(KREMLIN_HOME)/kremlib --include $(HACL_HOME)/code/lib/kremlin --include $(HACL_HOME)/code/experimental/utils --include $(HACL_HOME)/specs --include $(HACL_HOME)/specs/experimental --use_hints $^


record-hints: Hacl.Hash.SHA2.L256.fst
	$(FSTAR) --include $(FSTAR_HOME)/ulib/hyperstack --include $(KREMLIN_HOME)/kremlib --include $(HACL_HOME)/code/lib/kremlin --include $(HACL_HOME)/code/experimental/utils --include $(HACL_HOME)/specs --include $(HACL_HOME)/specs/experimental --record_hints $^


build:
	mkdir -p sha2-c
	$(KREMLIN_HOME)/krml -tmpdir sha2-c \
		-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/code/experimental/utils \
		-I $(HACL_HOME)/specs -I $(HACL_HOME)/specs/experimental \
		Hacl.Test.SHA2_256.fst -o sha2.exe -no-prefix Hacl.Test.SHA2_256 -no-prefix SHA2_256 \
		-drop 'Hacl.Cast' -drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
		-drop 'Hacl.Spec.Endianness' -drop 'Hacl.Endianness' -drop 'Spec.Lib' -drop 'Spec.Loops' -drop 'Seq.Create' -drop 'Spec.SHA2' \
		-drop Prims -drop FStar Hacl.Test.SHA2_256.fst \
		-no-prefix 'Hacl.Utils.Experimental' -no-prefix 'Hacl.Hash.SHA2.L256' -no-prefix 'SHA2_256'\
		-bundle "SHA2_256=Hacl.Utils.Experimental,Hacl.Hash.SHA2.L256,SHA2_256" \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -ccopt -Wno-error=strict-aliasing -ccopt -march=native -ccopt -std=gnu99 $(VERBOSE)
	./sha2.exe


build512:
	mkdir -p sha2-512-c
	$(KREMLIN_HOME)/krml -tmpdir sha2-512-c \
		-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/code/experimental/utils \
		-I $(HACL_HOME)/specs -I $(HACL_HOME)/specs/experimental \
		Hacl.Test.SHA2_512.fst -o sha2.exe -no-prefix Hacl.Test.SHA2_512 -no-prefix SHA2_512 \
		-drop 'Hacl.Cast' -drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
		-drop 'Hacl.Spec.Endianness' -drop 'Hacl.Endianness' -drop 'Spec.Lib' -drop 'Spec.Loops' -drop 'Seq.Create' -drop 'Spec.SHA2' \
		-drop Prims -drop FStar Hacl.Test.SHA2_512.fst \
		-no-prefix 'Hacl.Utils.Experimental' -no-prefix 'Hacl.Hash.SHA2.L512' -no-prefix 'SHA2_512'\
		-bundle "SHA2_512=Hacl.Utils.Experimental,Hacl.Hash.SHA2.L512,SHA2_512" \
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
	rm -rf sha2-512-c
