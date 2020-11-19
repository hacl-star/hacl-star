HACL_HOME=../..

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: dist/bignum-test.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include ../../Makefile.local

CFLAGS += -I ../../../lib/c -I ../../lib/c -march=native -mtune=native -O3
export CFLAGS

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.
dist/libbignum.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

BIGNUM_BUNDLE=-bundle Hacl.Bignum,Hacl.Bignum.*[rename=Hacl_Bignum] -static-header Hacl.Bignum,Hacl.Bignum.*

dist/Makefile.basic: $(filter-out %prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o libbignum.a $(BASE_FLAGS) $(BIGNUM_BUNDLE) \
	-tmpdir dist \
	-add-include '"lib_intrinsics.h"' \
	-fbuiltin-uint128 \
	-skip-compilation

dist/bignum-test.exe: $(HACL_HOME)/tests/bignum4096-test.o dist/libbignum.a

%.exe:
	$(CC) $(CFLAGS) $^ -o $@

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
