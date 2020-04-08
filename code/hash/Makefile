HACL_HOME=../..

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: dist/sha2-test.exe

test: all
	dist/sha2-test.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include ../../Makefile.local

#BASE_FLAGS+= -funroll-loops 4

CFLAGS += -I../../../lib/c -I../../lib/c -march=native -mtune=native -O3
export CFLAGS

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.
dist/libhash.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o libhash.a $(BASE_FLAGS) $(HASH_BUNDLE) -bundle Hacl.Impl.SHA2.Core=* \
	  -add-include '"libintvector.h"' \
	  -tmpdir dist \
	  -skip-compilation

dist/sha2-test.exe: $(HACL_HOME)/tests/sha2-test.o dist/libhash.a

%.exe:
	$(CC) $(CFLAGS) -flto $^ -o $@ -lcrypto

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
