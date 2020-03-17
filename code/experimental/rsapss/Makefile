HACL_HOME=../../..

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: dist/rsapss-test.exe

test: all
	dist/rsapss-test.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include ../../../Makefile.local

FSTAR_ROOTS += Hacl.Test.RSAPSS.fst

CFLAGS += -I $(HACL_HOME)/lib/c -march=native -mtune=native -O3
export CFLAGS

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.
dist/librsapss.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic OBJS=$(notdir $^) $(notdir $@)

SHA2_BUNDLE=-bundle Hacl.Hash.SHA2=Hacl.Hash.*
RSAPSS_BUNDLE=-bundle Hacl.RSAPSS+Hacl.Bignum.Convert=Hacl.Bignum.*,Hacl.Bignum,Hacl.Impl.MGF,Hacl.Impl.RSAPSS[rename=Hacl_RSAPSS]

HAND_WRITTEN_C_FILES = c/Hacl_Bignum_Base.c

dist/Makefile.basic: $(filter-out %prims.krml,$(ALL_KRML_FILES)) $(HAND_WRITTEN_C_FILES)
	mkdir -p $(dir $@)
	cp $(HAND_WRITTEN_C_FILES) $(dir $@)
	$(KRML) -tmpdir $(dir $@) -skip-compilation \
	  $(filter %.krml,$^) \
	  -bundle Hacl.Bignum.Base= \
	  $(BASE_FLAGS) $(SHA2_BUNDLE) $(RSAPSS_BUNDLE) \
	  -no-prefix 'Hacl.Test.RSAPSS' \
	  -add-include '<stdbool.h>' \
	  -add-include '<stdint.h>' \
	  -add-include '"kremlin/internal/target.h"' \
	  $(notdir $(HAND_WRITTEN_C_FILES)) \
	  -o librsapss.a

dist/%.o: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

dist/rsapss-test.exe: dist/Hacl_Test_RSAPSS.o \
	$(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a $(HACL_HOME)/lib/c/Lib_PrintBuffer.o dist/librsapss.a

rsapss-perf-test.exe: test-perf-rsapss.o \
	$(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a dist/librsapss.a


%.exe:
	$(CC) $(CFLAGS) $^ -o $@

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
