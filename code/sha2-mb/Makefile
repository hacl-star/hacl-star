HACL_HOME=../..

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: dist/sha2-mb-test.exe

test: all
	dist/sha2-mb-test.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include ../../Makefile.local

#BASE_FLAGS+= -funroll-loops 4

CFLAGS += -I../../../lib/c -I../../lib/c -I ../hash/dist -march=native -mtune=native -O3
export CFLAGS

SHA2MB_BUNDLE=-bundle Hacl.Impl.SHA2.Generic=Hacl.Impl.SHA2.*,Hacl.Hash.*[rename=Hacl_SHA2_Generic] -static-header Hacl.Impl.SHA2.Generic

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.
dist/libsha2mb.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o libsha2mb.a $(BASE_FLAGS) $(SHA2MB_BUNDLE) \
	  -add-include '"libintvector.h"' \
	  -tmpdir dist \
	  -skip-compilation

dist/sha2-mb-test.exe: $(HACL_HOME)/tests/sha2-mb-test.o dist/libsha2mb.a

%.exe:
	$(CC) $(CFLAGS) $^ -o $@ -lcrypto

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
