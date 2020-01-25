HACL_HOME=../..

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: dist/Makefile.basic

test: all

# Defines rules for producing .checked, .krml, .depend, etc.
include ../../Makefile.local

CFLAGS += -I../../lib/c -mavx -mavx2
export CFLAGS

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.
BLAKE2_BUNDLE=-bundle Hacl.Impl.Blake2.Constants -static-header Hacl.Impl.Blake2.Constants -bundle 'Hacl.Impl.Blake2.\*'

dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^  $(BASE_FLAGS) $(BLAKE2_BUNDLE) \
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

dist/blake2.exe: dist/Makefile.basic blake2-test.c
	$(CC) -O3 -march=native -mtune=native -I dist -I ../../lib/c -I ../../../kremlin/include -I ../../../kremlin/kremlib/c -I ../../../kremlin/kremlib/dist/minimal  dist/Hacl_Blake2s_32.c dist/Hacl_Blake2b_32.c  dist/Hacl_Blake2s_128.c dist/Hacl_Blake2b_256.c blake2-test.c -o dist/blake2.exe

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
	rm -rf dist .output
