HACL_HOME=$(realpath ../..)

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: dist/Makefile.basic

test: all dist/blake2-test.exe
	dist/blake2-test.exe

test32: all dist/blake2-test32.exe
	dist/blake2-test32.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include $(HACL_HOME)/Makefile.local

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.

BLAKE2_BUNDLE= -bundle Hacl.Blake2b_32=Hacl.Impl.Blake2.\* \
  -bundle Hacl.Blake2s_32=Hacl.Impl.Blake2.\* \
  -bundle Hacl.Blake2s_128=Hacl.Impl.Blake2.\* \
  -bundle Hacl.Blake2b_256=Hacl.Impl.Blake2.\*


dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^  $(BASE_FLAGS) $(BLAKE2_BUNDLE) \
	  -funroll-loops 12 \
	  -fbuiltin-uint128 \
	  -tmpdir dist \
	  -skip-compilation \
	  -ccopts -std=gnu11,-g,-O3 \
	  -I "../../../karamel/include" \
	  -I "../../lib/c" \
	  -add-include '"kremlin/internal/target.h"' \
	  -add-include '<stdbool.h>' \
	  -add-include '"libintvector.h"' \
	  -skip-compilation

dist/blake2-test.exe: dist/Makefile.basic blake2-test.c
	$(CC) -O3 -march=native -mtune=native -DVEC128 -DVEC256 -I ../../dist/gcc64-only -I dist -I ../../lib/c -I ../../dist/karamel/include -I ../../dist/karamel/krmllib/c -I ../../dist/karamel/krmllib/dist/minimal -I ../../tests ../../dist/gcc64-only/Lib_Memzero0.c dist/Hacl_Blake2b_32.c  dist/Hacl_Blake2s_32.c dist/Hacl_Blake2s_128.c dist/Hacl_Blake2b_256.c blake2-test.c -o dist/blake2-test.exe

dist/blake2-test32.exe: dist/Makefile.basic blake2-test.c
	$(CC) -O3 -march=native -mtune=native -UVEC128 -UVEC256 -I ../../dist/gcc64-only -I dist -I ../../lib/c -I ../../dist/karamel/include -I ../../dist/karamel/krmllib/c -I ../../dist/karamel/krmllib/dist/minimal -I ../../tests ../../dist/gcc64-only/Lib_Memzero0.c dist/Hacl_Blake2b_32.c  dist/Hacl_Blake2s_32.c blake2-test.c -o dist/blake2-test32.exe

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
	rm -rf dist .output
