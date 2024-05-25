HACL_HOME=$(realpath ../..)

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: \
	dist/gf128-ni-test.exe

test: all
	dist/gf128-ni-test.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include ../../Makefile.local

CFLAGS += -I$(HACL_HOME)/lib/c -msse4.1 -mpclmul
export CFLAGS

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.
dist/libgf128.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

GF128_NI_BUNDLE=-bundle Hacl.Gf128.NI=Hacl.Impl.Gf128.FieldNI

# Note: POLY_BUNDLE is found in Makefile.common -- shared definition.
dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o libgf128.a $(BASE_FLAGS) $(GF128_PRECOMP_BUNDLE) $(GF128_NI_BUNDLE) \
	  -tmpdir dist \
	  -ccopts -std=gnu11,-g,-O3 \
	  -add-include '"libintvector.h"' \
	  -add-include '<stdbool.h>' \
	  -skip-compilation

dist/gf128-ni-test.exe: $(HACL_HOME)/tests/gf128-ni-test.o dist/libgf128.a

%.exe:
	$(CC) $(CFLAGS) $^ -o $@

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
