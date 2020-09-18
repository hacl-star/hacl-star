HACL_HOME=../..

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: dist/rsapss-test.exe

test: all
	dist/rsapss-test.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include ../../Makefile.local

CFLAGS += -I ../../../lib/c -I ../../lib/c -march=native -mtune=native -O3
export CFLAGS

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.
dist/librsapss.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

SHA2_BUNDLE=-bundle Hacl.Hash.SHA2=Hacl.Hash.*
RSAPSS_BUNDLE=-bundle Hacl.RSAPSS=Hacl.Bignum.*,Hacl.Bignum,Hacl.Impl.RSAPSS.*,Hacl.Impl.RSAPSS[rename=Hacl_RSAPSS]

dist/Makefile.basic: $(filter-out %prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o librsapss.a $(BASE_FLAGS) $(SHA2_BUNDLE) $(RSAPSS_BUNDLE) \
	-tmpdir dist \
	-add-include '"lib_intrinsics.h"' \
	-fbuiltin-uint128 \
	-skip-compilation

dist/rsapss-test.exe: $(HACL_HOME)/tests/rsapss-test.o dist/librsapss.a

%.exe:
	$(CC) $(CFLAGS) $^ -o $@

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
