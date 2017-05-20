HACL_HOME    ?= ../../..
FSTAR_HOME   ?= $(HACL_HOME)/dependencies/FStar
KREMLIN_HOME ?= $(HACL_HOME)/dependencies/kremlin

FSTAR ?= $(FSTAR_HOME)/bin/fstar.exe

KRML_BIN=$(KREMLIN_HOME)/_build/src/Kremlin.native
KRML=$(KRML_BIN) $(KREMLIN_ARGS)

HINTS_ENABLED= --use_hints


FSTARB=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
        --include $(HACL_HOME)/code/lib/kremlin --include $(KREMLIN_HOME)/kremlib \
         --include $(HACL_HOME)/specs  \
        $(HINTS_ENABLED) $(OTHERFLAGS)

FSTAR_CT=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
        --include $(HACL_HOME)/code/lib  --include $(KREMLIN_HOME)/kremlib \
        --include $(HACL_HOME)/specs

# Files for verification
SHA2_FILES = \
	Hacl.Hash.Lib.LoadStore.fst \
	Hacl.Hash.Lib.Create.fst \
	Hacl.Hash.SHA2_512.Lemmas.fst \
	Hacl.Hash.SHA2_512.fst \
	Hacl.Hash.SHA2_256.Lemmas.fst \
	Hacl.Hash.SHA2_256.fst


# Full typechecking against the transparent integer interface
%.fst-verify: %.fst
	$(FSTARB) $^

%.fsti-verify: %.fsti
	$(FSTARB) $^

# CI
all-ci: test

# Verification
all-verif: $(addsuffix -verify, $(SHA2_FILES)) # This is too costly for the CI

# Lax typechecking against the restricted integer interface
%.fst-ct: %.fst
	$(FSTAR_CT) --lax $^

all-ct: $(addsuffix -ct, $(SHA2_FILES))

# Extraction
extract-c: sha2-c/SHA2_256.c sha2-c/SHA2_512.c

test: test-sha2_256.exe test-sha2_512.exe

clean:
	rm -rf *~ *.exe *.exe.dSYM
	rm -rf sha2-c


# Common call to Kremlin for both extraction and tests
KRML_COMMON_SHA2_256 = \
$(KRML) -verbose -tmpdir sha2-c \
		-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/specs \
		-I $(HACL_HOME)/code/hash \
		-drop Prims -drop FStar \
		-drop 'Hacl.Cast' -drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
		-drop 'Hacl.Spec.Endianness' -drop 'Hacl.Endianness' \
		-drop 'Seq.Create' -drop 'Spec.\*' \
		-drop 'Hacl.Hash.SHA2_256.Lemmas' \
		-bundle "SHA2_256=Hacl.Hash.Lib.Create,Hacl.Hash.Lib.LoadStore,Hacl.Hash.SHA2_256,SHA2_256" \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -ccopt -Wno-error=strict-aliasing -ccopt -march=native -ccopt -std=gnu99

KRML_COMMON_SHA2_512 = \
$(KRML) -verbose -tmpdir sha2-c \
		-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/specs \
		-I $(HACL_HOME)/code/hash \
		-drop Prims -drop FStar \
		-drop 'Hacl.Cast' -drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
		-drop 'Hacl.Spec.Endianness' -drop 'Hacl.Endianness' \
		-drop 'Seq.Create' -drop 'Spec.\*' \
		-drop 'Hacl.Hash.SHA2_512.Lemmas' \
		-bundle "SHA2_512=Hacl.Hash.Lib.Create,Hacl.Hash.Lib.LoadStore,Hacl.Hash.SHA2_512,SHA2_512" \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -ccopt -Wno-error=strict-aliasing -ccopt -march=native -ccopt -std=gnu99


sha2-c/SHA2_256.c:
	mkdir -p sha2-c
	$(KRML_COMMON_SHA2_256) -skip-compilation SHA2_256.fst

sha2-c/SHA2_512.c:
	mkdir -p sha2-c
	$(KRML_COMMON_SHA2_512) -skip-compilation SHA2_512.fst


test-sha2_256.exe: Hacl.Hash.SHA2_256.Lemmas.fst Hacl.Hash.SHA2_256.fst SHA2_256.fst Hacl.Test.SHA2_256.fst
	mkdir -p sha2-c
	$(KRML_COMMON_SHA2_256) -o test-sha2_256.exe -no-prefix 'Hacl.Test.SHA2_256' $^
	./test-sha2_256.exe

test-sha2_512.exe: Hacl.Hash.SHA2_512.Lemmas.fst Hacl.Hash.SHA2_512.fst SHA2_512.fst Hacl.Test.SHA2_512.fst
	mkdir -p sha2-c
	$(KRML_COMMON_SHA2_512) -o test-sha2_512.exe -no-prefix 'Hacl.Test.SHA2_512' $^
	./test-sha2_512.exe
