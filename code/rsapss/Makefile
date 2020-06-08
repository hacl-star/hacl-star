HACL_HOME=../..

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: dist/rsapss-test.exe

test: all
	dist/rsapss-test.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include ../../Makefile.local

CFLAGS += -I $(HACL_HOME)/lib/c -march=native -mtune=native -O3
export CFLAGS

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.
dist/librsapss.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

SHA2_BUNDLE=-bundle Hacl.Hash.SHA2=Hacl.Hash.*
RSAPSS_BUNDLE=-bundle Hacl.RSAPSS+Hacl.Bignum.Convert=Hacl.Bignum.*,Hacl.Bignum,Hacl.Impl.MGF,Hacl.Impl.RSAPSS[rename=Hacl_RSAPSS]

HAND_WRITTEN_C_FILES = c/hacl_bignum_base.h

dist/Makefile.basic: $(filter-out %prims.krml,$(ALL_KRML_FILES))
	mkdir -p $(dir $@)
	cp $(HAND_WRITTEN_C_FILES) $(dir $@)
	$(KRML) -tmpdir $(dir $@) -skip-compilation \
	  $(filter %.krml,$^) \
	  -drop Hacl.Bignum.Base \
	  $(BASE_FLAGS) $(SHA2_BUNDLE) $(RSAPSS_BUNDLE) \
	  -no-prefix 'Hacl.Test.RSAPSS' \
	  -add-include '"hacl_bignum_base.h"' \
	  -o librsapss.a

dist/rsapss-test.exe: $(HACL_HOME)/tests/rsapss-test.o dist/librsapss.a

%.exe:
	$(CC) $(CFLAGS) $^ -o $@

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
