include ../Makefile.include

KRML_BIN=$(KREMLIN_HOME)/_build/src/Kremlin.native
KRML=$(KRML_BIN) $(KREMLIN_ARGS)

# Files for verification
HMAC_SHA2_FILES = Hacl.HMAC.SHA2_256.fst
#	               HMAC_SHA2_256.fst

FSTAR_INCLUDES+=--include ../hash

ct: $(addsuffix -lax, $(HMAC_SHA2_FILES))
hints: $(addsuffix .hints, $(HMAC_SHA2_FILES))
verify: $(addsuffix -verify, $(HMAC_SHA2_FILES))
all-ct: ct
all-ver: verify 
all-ci: verify
all-hints: hints

extract-c: hmac-c/HMAC_SHA2_256.c

test: test-hmac_sha2_256.exe

clean:
	rm -rf *~ *.exe *.exe.dSYM
	rm -rf hmac-c



# Common call to Kremlin for both extraction and tests
KREMLIN_ARGS+= \
		-verbose -tmpdir hmac-c \
		-I $(HACL_HOME)/code/hash \
		-drop Prims -drop FStar \
		-drop 'Hacl.Cast' -drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
		-drop 'Hacl.Spec.Endianness' -drop 'Hacl.Endianness' \
		-drop 'Seq.Create' -drop 'Spec.\*' \
		-drop 'Hacl.Hash.SHA2_256.Lemmas' \
		-bundle "HMAC_SHA2_256=Hacl.Hash.Lib.Create,Hacl.Hash.Lib.LoadStore,Hacl.Hash.SHA2_256,Hacl.HMAC.SHA2_256,HMAC_SHA2_256" \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -ccopt -Wno-error=strict-aliasing -ccopt -march=native -ccopt -std=gnu99


hmac-c/HMAC_SHA2_256.c: HMAC_SHA2_256.fst
	mkdir -p hmac-c
	$(KREMLIN) $(KREMLIN_ARGS) -skip-compilation -no-prefix 'HMAC_SHA2_256' $^


test-hmac_sha2_256.exe: Hacl.Test.HMAC.SHA2_256.fst
	mkdir -p hmac-c
	$(KREMLIN) $(KREMLIN_ARGS) -o test-hmac_sha2_256.exe -no-prefix 'Hacl.Test.HMAC.SHA2_256' $^
	./test-hmac_sha2_256.exe
