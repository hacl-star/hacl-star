HACL_HOME    ?= ../../..
FSTAR_HOME   ?= $(HACL_HOME)/dependencies/FStar
KREMLIN_HOME ?= $(HACL_HOME)/dependencies/kremlin

FSTAR ?= $(FSTAR_HOME)/bin/fstar.exe

KRML_BIN=$(KREMLIN_HOME)/_build/src/Kremlin.native
KRML=$(KRML_BIN) $(KREMLIN_ARGS) -ccopt -Wno-unknown-warning-option -ccopt -Wno-tautological-constant-out-of-range-compare



SHA2_FILES = \
	Hacl.Hash.SHA2_256.Lemmas.fst \
	Hacl.Hash.SHA2_256.fst \
	SHA2_256.fst \
	Hacl.Hash.SHA2_512.Lemmas.fst \
	Hacl.Hash.SHA2_512.fst \
	SHA2_512.fst



# Verification
verify: verification

# Extraction
extract-c: tests #sha2-c/SHA2_256.c sha2-c/SHA2_512.c

# Test vectors
tests: test-sha2_256.exe test-sha2_512.exe

# CI
all-ci:

# Reset
clean:
	rm -rf *~ *.exe *.exe.dSYM
	rm -rf sha2-c



verification: $(SHA2_FILES)
	$(FSTAR) --include $(FSTAR_HOME)/ulib/hyperstack --include $(KREMLIN_HOME)/kremlib --include $(HACL_HOME)/code/lib/kremlin --include $(HACL_HOME)/code/experimental/utils --include $(HACL_HOME)/specs --use_hints $^


record-hints: $(SHA2_FILES)
	$(FSTAR) --include $(FSTAR_HOME)/ulib/hyperstack --include $(KREMLIN_HOME)/kremlib --include $(HACL_HOME)/code/lib/kremlin --include $(HACL_HOME)/code/experimental/utils --include $(HACL_HOME)/specs --use_hints --record_hints $^



sha2-c/SHA2_256.c:
	mkdir -p sha2-c
	$(KRML) -verbose -tmpdir sha2-c \
		-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/code/experimental/utils -I $(HACL_HOME)/specs \
		SHA2_256.fst \
		-drop 'Hacl.Cast' -drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
		-drop 'Hacl.Spec.Endianness' -drop 'Hacl.Endianness' -drop 'Spec.Lib' -drop 'Spec.Loops' -drop 'Seq.Create' -drop 'Spec.\*' \
		-drop 'Hacl.Hash.SHA2_256.Lemmas' -drop Prims -drop FStar \
		-bundle "SHA2_256=Hacl.Utils.Experimental,Hacl.Hash.SHA2_256,SHA2_256" \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -ccopt -Wno-error=strict-aliasing -ccopt -march=native -ccopt -std=gnu99 -skip-compilation


sha2-c/SHA2_512.c:
	mkdir -p sha2-c
	$(KRML) -verbose -tmpdir sha2-c \
		-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/code/experimental/utils -I $(HACL_HOME)/specs \
		SHA2_512.fst \
		-drop 'Hacl.Cast' -drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
		-drop 'Hacl.Spec.Endianness' -drop 'Hacl.Endianness' -drop 'Spec.Lib' -drop 'Spec.Loops' -drop 'Seq.Create' -drop 'Spec.\*' \
		-drop 'Hacl.Hash.SHA2_512.Lemmas' -drop Prims -drop FStar \
		-bundle "SHA2_512=Hacl.Utils.Experimental,Hacl.Hash.SHA2_512,SHA2_512" \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -ccopt -Wno-error=strict-aliasing -ccopt -march=native -ccopt -std=gnu99 -skip-compilation


test-sha2_256.exe:
	mkdir -p sha2-c
	$(KRML) -verbose -tmpdir sha2-c \
		-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/code/experimental/utils -I $(HACL_HOME)/specs \
		Hacl.Test.SHA2_256.fst -o sha2_256.exe -no-prefix Hacl.Test.SHA2_256 -no-prefix SHA2_256 \
		-drop 'Hacl.Cast' -drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
		-drop 'Hacl.Spec.Endianness' -drop 'Hacl.Endianness' -drop 'Spec.Lib' -drop 'Spec.Loops' -drop 'Seq.Create' -drop 'Spec.SHA2_256' \
		-drop 'Hacl.Hash.SHA2_256.Lemmas' -drop Prims -drop FStar Hacl.Test.SHA2_256.fst \
		-no-prefix 'Hacl.Utils.Experimental' -no-prefix 'SHA2_256' \
		-bundle "SHA2_256=Hacl.Utils.Experimental,Hacl.Hash.SHA2_256,SHA2_256" \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -ccopt -Wno-error=strict-aliasing -ccopt -march=native -ccopt -std=gnu99
	./sha2_256.exe


test-sha2_512.exe:
	mkdir -p sha2-c
	$(KRML) -verbose -tmpdir sha2-c \
		-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/code/experimental/utils -I $(HACL_HOME)/specs \
		SHA2_512.fst Hacl.Test.SHA2_512.fst -o sha2_512.exe -no-prefix Hacl.Test.SHA2_512 -no-prefix SHA2_512 \
		-drop 'Hacl.Cast' -drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
		-drop 'Hacl.Spec.Endianness' -drop 'Hacl.Endianness' -drop 'Spec.Lib' -drop 'Spec.Loops' -drop 'Seq.Create' -drop 'Spec.SHA2_512' \
		-drop 'Hacl.Hash.SHA2_512.Lemmas' -drop Prims -drop FStar Hacl.Test.SHA2_512.fst \
		-no-prefix 'Hacl.Utils.Experimental' -no-prefix 'SHA2_512' \
		-bundle "SHA2_512=Hacl.Utils.Experimental,Hacl.Hash.SHA2_512,SHA2_512" \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -ccopt -Wno-error=strict-aliasing -ccopt -march=native -ccopt -std=gnu99
	./sha2_512.exe
