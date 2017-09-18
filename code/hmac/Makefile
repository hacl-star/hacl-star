include ../../Makefile.include

# Files for verification
HMAC_SHA2_FILES= \
	Hacl.HMAC.SHA2_256.fst \
	HMAC_SHA2_256.fst

FSTAR_INCLUDES+=--include ../hash

# Parameter for interactive mode
%.fst-in:
	@echo $(OPTIONS) --hint_info \
	$(FSTAR_INCLUDES)

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
		-drop Prims \
		-drop Hacl.Cast,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128 \
		-drop Hacl.Spec.Endianness,Hacl.Endianness,Seq.Create,Spec.*,Hacl.Hash.SHA2_256.Lemmas \
		-bundle "HMAC_SHA2_256=Hacl.Hash.Lib.Create,Hacl.Hash.Lib.LoadStore,Hacl.Hash.SHA2_256,Hacl.HMAC.SHA2_256,HMAC_SHA2_256" \
		-ccopt -Wno-error=strict-aliasing -ccopt -march=native -ccopt -std=gnu99 \
		$(KREMLIN_TESTLIB)

hmac-c/out.krml: HMAC_SHA2_256.fst Hacl.Test.HMAC.SHA2_256.fst
	$(KREMLIN) $(KREMLIN_ARGS) -skip-compilation -no-prefix HMAC_SHA2_256 \
	$^ -o $@

hmac-c/HMAC_SHA2_256.c: hmac-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -skip-compilation -no-prefix HMAC_SHA2_256 \
		$^ -o $@

test-hmac_sha2_256.exe: hmac-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -o test-hmac_sha2_256.exe -no-prefix Hacl.Test.HMAC.SHA2_256 \
		$^ -o $@
	./test-hmac_sha2_256.exe
