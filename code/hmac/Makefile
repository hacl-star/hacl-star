include ../Makefile.include

KRML_BIN=$(KREMLIN_HOME)/_build/src/Kremlin.native
KRML=$(KRML_BIN) $(KREMLIN_ARGS)


HINTS_ENABLED= --use_hints


FSTARB=$(FSTAR_BASE) \
        --include $(HACL_HOME)/code/lib/kremlin --include $(KREMLIN_HOME)/kremlib \
        --include $(HACL_HOME)/specs \
	--include $(HACL_HOME)/code/hash

FSTAR_CT=$(FSTAR_BASE) \
        --include $(HACL_HOME)/code/lib  --include $(KREMLIN_HOME)/kremlib \
	--include $(HACL_HOME)/code/hash \
        --include $(HACL_HOME)/specs


# Files for verification
HMAC_SHA2_FILES = Hacl.HMAC.SHA2_256.fst
#	               HMAC_SHA2_256.fst


# Full typechecking against the transparent integer interface
%.fst-ver: %.fst
	$(FSTARB) $^

%.fsti-ver: %.fsti
	$(FSTARB) $^

# Verification
all-ver: $(addsuffix -ver, $(HMAC_SHA2_FILES))

# Lax typechecking against the restricted integer interface
%.fst-ct: %.fst
	$(FSTAR_CT) --lax $^

all-ct: $(addsuffix -ct, $(HMAC_SHA2_FILES))

# CI
all-ci: all-ver

extract-c: hmac-c/HMAC_SHA2_256.c

test: test-hmac_sha2_256.exe

clean:
	rm -rf *~ *.exe *.exe.dSYM
	rm -rf hmac-c



# Common call to Kremlin for both extraction and tests
KRML_COMMON_HMAC_SHA2_256 = \
$(KRML) -verbose -tmpdir hmac-c \
		-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/specs \
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
	$(KRML_COMMON_HMAC_SHA2_256) -skip-compilation -no-prefix 'HMAC_SHA2_256' $^


test-hmac_sha2_256.exe: Hacl.Test.HMAC.SHA2_256.fst
	mkdir -p hmac-c
	$(KRML_COMMON_HMAC_SHA2_256) -o test-hmac_sha2_256.exe -no-prefix 'Hacl.Test.HMAC.SHA2_256' $^
	./test-hmac_sha2_256.exe
