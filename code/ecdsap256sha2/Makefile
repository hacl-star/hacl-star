HACL_HOME=../..

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: dist/Hacl_Test_ECDSA.exe

test: all
	dist/Hacl_Test_ECDSA.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include ../../Makefile.local

FSTAR_ROOTS += ../tests/Hacl.Test.ECDSA.fst

#BASE_FLAGS+= -funroll-loops 4

CFLAGS += -I ../../../lib/c -march=native -mtune=native -O3
export CFLAGS

dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o libecdsa.a $(BASE_FLAGS) $(ECDSA_BUNDLE) \
	  -tmpdir dist \
	  -add-include '"lib_intrinsics.h"' \
	  -no-prefix 'Hacl.Test.ECDSA' \
	  -skip-compilation

# An archive with all the compiled code in this directory.
# We don't want Hacl_Test_ECDSA.o to be included so we redefine OBJS
dist/libecdsa.a: dist/Hacl_ECDSA.o
	$(MAKE) -C dist -f Makefile.basic OBJS=$(notdir $^) $(notdir $@)

dist/%.o: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic $(notdir $@)

dist/Hacl_Test_ECDSA.exe: dist/Hacl_Test_ECDSA.o \
	$(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a dist/libecdsa.a

%.exe:
	$(CC) $(CFLAGS) -flto $^ -o $@

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
