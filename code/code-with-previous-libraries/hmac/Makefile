include ../../Makefile.include

# Files for verification
HMAC_SHA2_FILES= \
	Hacl.Impl.HMAC.SHA2_256.fst \
	Hacl.HMAC.SHA2_256.fst

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

extract-c: hmac-sha256-c/Hacl_HMAC_SHA2_256.c hmac-sha384-c/Hacl_HMAC_SHA2_384.c hmac-sha512-c/Hacl_HMAC_SHA2_512.c

test: test-hmac_sha2_256.exe

clean:
	rm -rf *~ *.exe *.exe.dSYM
	rm -rf hmac-*

# Common call to Kremlin for both extraction and tests
KREMLIN_ARGS+= \
		-verbose \
		-I $(HACL_HOME)/code/hash \
		-ccopt -Wno-error=strict-aliasing -ccopt -march=native -ccopt -std=gnu99 \
		$(KREMLIN_TESTLIB)

hmac-sha256-c/out.krml: Hacl.HMAC.SHA2_256.fst Hacl.Test.HMAC.SHA2_256.fst
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir hmac-sha256-c -skip-translation \
	$^ -o $@

hmac-sha256-c/Hacl_HMAC_SHA2_256.c: hmac-sha256-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir hmac-sha256-c \
	-bundle "Hacl.HMAC.SHA2_256=*" -minimal -add-include '"kremlib.h"' \
	-skip-compilation \
	$^ -o $@

test-hmac_sha2_256.exe: hmac-sha256-c/Hacl_HMAC_SHA2_256.c hmac-sha256-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir hmac-sha256-c -o test-hmac_sha2_256.exe \
	  -no-prefix Hacl.Test.HMAC.SHA2_256 \
	  -minimal -add-include '"kremlib.h"' -bundle Hacl.Test.HMAC.SHA2_256=* \
	  -library Hacl.HMAC.SHA2_256 \
	  $^ -o $@
	./test-hmac_sha2_256.exe

hmac-sha384-c/out.krml: Hacl.HMAC.SHA2_384.fst
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir hmac-sha384-c -skip-translation \
	$^ -o $@

hmac-sha384-c/Hacl_HMAC_SHA2_384.c: hmac-sha384-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir hmac-sha384-c \
	-bundle "Hacl.HMAC.SHA2_384=*" -minimal -add-include '"kremlib.h"' \
	-skip-compilation \
	$^ -o $@

hmac-sha512-c/out.krml: Hacl.HMAC.SHA2_512.fst
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir hmac-sha512-c -skip-translation \
	$^ -o $@

hmac-sha512-c/Hacl_HMAC_SHA2_512.c: hmac-sha512-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir hmac-sha512-c \
	-bundle "Hacl.HMAC.SHA2_512=*" -minimal -add-include '"kremlib.h"' \
	-skip-compilation \
	$^ -o $@
