HACL_HOME=../..

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: dist/chacha20-test.exe dist/chacha20-vec-test.exe

test: all
	dist/chacha20-test.exe
	dist/chacha20-vec-test.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include ../../Makefile.local

CFLAGS += -I../../../lib/c -mavx -mavx2
export CFLAGS

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.
dist/libchacha.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o libchacha.a $(BASE_FLAGS) $(CHACHA20_BUNDLE) \
	  -tmpdir dist \
	  -ccopts -std=gnu11,-g,-O3 \
	  -add-include '"libintvector.h"' \
	  -skip-compilation

dist/chacha20-test.exe: $(HACL_HOME)/tests/chacha20-test.o dist/libchacha.a

dist/chacha20-vec-test.exe: $(HACL_HOME)/tests/chacha20-vec-test.o dist/libchacha.a

%.exe:
	$(CC) $^ $(KREMLIB_A) -o $@

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
