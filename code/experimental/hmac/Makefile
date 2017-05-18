HACL_HOME    ?= ../../..
FSTAR_HOME   ?= $(HACL_HOME)/dependencies/FStar
KREMLIN_HOME ?= $(HACL_HOME)/dependencies/kremlin

FSTAR ?= $(FSTAR_HOME)/bin/fstar.exe

KRML_BIN=$(KREMLIN_HOME)/_build/src/Kremlin.native
KRML=$(KRML_BIN) $(KREMLIN_ARGS)


# Files for verification
HMAC_SHA2_FILES = \
	Hacl.HMAC.SHA2_256.fst \
	HMAC_SHA2_256.fst


# Common call to Kremlin for both extraction and tests
KRML_COMMON_HMAC_SHA2_256 = \
$(KRML) -verbose -tmpdir hmac-c \
		-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/specs \
		-I $(HACL_HOME)/code/experimental/hash -I $(HACL_HOME)/code/experimental/utils \
		-drop Prims -drop FStar \
		-drop 'Hacl.Cast' -drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
		-drop 'Hacl.Spec.Endianness' -drop 'Hacl.Endianness' \
		-drop 'Seq.Create' -drop 'Spec.\*' \
		-drop 'Hacl.Hash.SHA2_256.Lemmas' \
		-bundle "HMAC_SHA2_256=Hacl.Utils.Experimental,Hacl.Hash.SHA2_256,Hacl.HMAC.SHA2_256,HMAC_SHA2_256" \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -ccopt -Wno-error=strict-aliasing -ccopt -march=native -ccopt -std=gnu99



# Verification
verify: verification

# Extraction
extract-c: tests #hmac-c/HMAC_SHA2_256.c

# Test vectors
test: test-hmac_sha2_256.exe

# CI
all-ci:

# Reset
clean:
	rm -rf *~ *.exe *.exe.dSYM
	rm -rf hmac-c



verification: $(HMAC_SHA2_FILES)
	$(FSTAR) --include $(FSTAR_HOME)/ulib/hyperstack --include $(KREMLIN_HOME)/kremlib --include $(HACL_HOME)/code/lib/kremlin --include $(HACL_HOME)/code/experimental/utils --include $(HACL_HOME)/code/experimental/hash --include $(HACL_HOME)/specs --use_hints $^


record-hints: $(HMAC_SHA2_FILES)
	$(FSTAR) --include $(FSTAR_HOME)/ulib/hyperstack --include $(KREMLIN_HOME)/kremlib --include $(HACL_HOME)/code/lib/kremlin --include $(HACL_HOME)/code/experimental/utils --include $(HACL_HOME)/code/experimental/hash --include $(HACL_HOME)/specs --use_hints --record_hints $^ --hint_info


hmac-c/HMAC_SHA2_256.c:
	mkdir -p hmac-c
	$(KRML_COMMON_HMAC_SHA2_256) -skip-compilation -no-prefix 'HMAC_SHA2_256' HMAC_SHA2_256.fst


test-hmac_sha2_256.exe:
	mkdir -p hmac-c
	$(KRML_COMMON_HMAC_SHA2_256) -o test-hmac_sha2_256.exe -no-prefix 'Hacl.Test.HMAC.SHA2_256' Hacl.Test.HMAC.SHA2_256.fst
	./test-hmac_sha2_256.exe
