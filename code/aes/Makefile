HACL_HOME=../..

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: dist/Makefile.basic

test: all
	dist/aes128-bitslice-test.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include ../../Makefile.local

CFLAGS += -I../../lib/c -mavx -mavx2
export CFLAGS

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.

dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^  $(BASE_FLAGS) $(AES128_BITSLICE_BUNDLE) \
	  -funroll-loops 8 \
	  -fbuiltin-uint128 \
	  -tmpdir dist \
	  -ccopts -std=gnu11,-g,-O3 \
	  -I "../../../kremlin/include" \
	  -I "../../lib/c" \
	  -add-include '"kremlin/internal/target.h"' \
	  -add-include '<stdbool.h>' \
	  -add-include '"libintvector.h"' \
	  -skip-compilation

dist/aes128-bitslice.exe: dist/Makefile.basic $(HACL_HOME)/code/experimental/aes/aes128-bitslice-test.c
	$(CC) -O3 -march=native -mtune=native -I dist -I ../../lib/c -I ../../../kremlin/include -I ../../../kremlin/kremlib/c -I ../../../kremlin/kremlib/dist/minimal \
	dist/Hacl_AES128_Bitslice.c $(HACL_HOME)/code/experimental/aes/aes128-bitslice-test.c -o dist/aes128-bitslice.exe

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
	rm -rf dist .output
