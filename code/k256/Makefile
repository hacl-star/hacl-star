HACL_HOME=$(realpath ../..)

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: dist/libk256.a

# Defines rules for producing .checked, .krml, .depend, etc.
include $(HACL_HOME)/Makefile.local

FSTAR_ROOTS += $(HACL_HOME)/code/tests/Hacl.Test.K256.fst

CFLAGS += -I$(HACL_HOME)/lib/c -march=native -mtune=native -O3 -DCOMPILE_INTRINSICS
export CFLAGS

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.
dist/libk256.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

HASH_BUNDLE=-bundle Hacl.Hash.SHA2+Hacl.Hash.Core.SHA2+Hacl.Hash.Definitions=Hacl.Hash.*[rename=Hacl_Hash]
STREAMING_BUNDLE=-bundle Hacl.Streaming.*
BLAKE2_BUNDLE=-bundle Hacl.Impl.Blake2.Constants -static-header Hacl.Impl.Blake2.Constants -bundle 'Hacl.Impl.Blake2.\*'
K256_BUNDLE= -bundle Hacl.K256.Field,Hacl.Impl.K256.Finv[rename=Hacl_Bignum_K256] -static-header Hacl.K256.Field,Hacl.Impl.K256.Finv \
	-bundle 'Hacl.K256.ECDSA=Hacl.Impl.K256.*,Hacl.K256.*'

dist/Makefile.basic: $(filter-out %prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o libk256.a \
	-bundle Lib.PrintBuffer= \
	$(BASE_FLAGS) $(HASH_BUNDLE) $(STREAMING_BUNDLE) $(BLAKE2_BUNDLE) \
	$(BIGNUM_BUNDLE) $(K256_BUNDLE) \
	-tmpdir dist \
	-add-include '"lib_intrinsics.h"' \
	-no-prefix 'Hacl.Test.K256' \
	-fbuiltin-uint128 \
	-skip-compilation

dist/k256-test.exe: dist/libk256.a \
	$(KRML_HOME)/krmllib/dist/generic/libkrmllib.a $(HACL_HOME)/lib/c/Lib_PrintBuffer.c

%.exe:
	$(CC) $(CFLAGS) $^ -o $@

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
