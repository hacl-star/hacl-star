HACL_HOME=../../..

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: dist/rsapss-test.exe

test: all
	dist/rsapss-test.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include ../../../Makefile.local

CFLAGS += -I $(HACL_HOME)/lib/c
export CFLAGS

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.
dist/librsapss.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

SHA2_BUNDLE=-bundle Hacl.Hash.SHA2=Hacl.Hash.*
RSAPSS_BUNDLE=-bundle Hacl.RSAPSS+Hacl.Bignum.Convert=Hacl.Bignum.*,Hacl.Bignum,Hacl.Impl.MGF,Hacl.Impl.RSAPSS[rename=Hacl_RSAPSS]
RSAPSS_TEST_BUNDLE=-bundle Hacl.RSAPSS.Test

dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o librsapss.a $(BASE_FLAGS) $(SHA2_BUNDLE) \
	  $(RSAPSS_BUNDLE) $(RSAPSS_TEST_BUNDLE) \
	  -no-prefix 'Hacl.Test.RSAPSS' \
	  -tmpdir dist \
	  -ccopts -std=gnu11,-g,-O3 \
	  -add-include '"kremlin/internal/target.h"' \
	  -add-include '<stdbool.h>' \
	  -skip-compilation

dist/Hacl_Test_RSAPSS.o: dist/Makefile.basic

dist/rsapss-test.exe: $(HACL_HOME)/lib/c/Lib_PrintBuffer.o dist/Hacl_Test_RSAPSS.o dist/librsapss.a

%.exe:
	$(CC) $(CFLAGS) $^ -o $@ -L $(KREMLIN_HOME)/kremlib/dist/generic -lkremlib

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
