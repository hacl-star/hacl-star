HACL_HOME=../..

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: dist/sha2-vec-test.exe

test: all
	dist/sha2-vec-test.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include ../../Makefile.local

#BASE_FLAGS+= -funroll-loops 4

CFLAGS += -I../../../lib/c -I../../lib/c -I ../hash/dist -march=native -mtune=native -O3
export CFLAGS

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.
dist/libsha2vec.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o libsha2vec.a $(BASE_FLAGS) $(SHA2VEC_BUNDLE) \
	  -add-include '"libintvector.h"' \
	  -tmpdir dist \
	  -skip-compilation

dist/sha2-vec-test.exe: $(HACL_HOME)/tests/sha2-vec-test.o dist/libsha2vec.a

%.exe:
	$(CC) $(CFLAGS) $^ -o $@ -lcrypto

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
