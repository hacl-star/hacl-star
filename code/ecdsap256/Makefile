HACL_HOME=$(realpath ../..)

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: dist/p256-test.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include $(HACL_HOME)/Makefile.local

FSTAR_ROOTS += $(HACL_HOME)/code/tests/Hacl.Test.ECDSA.fst

CFLAGS += -I$(HACL_HOME)/lib/c -march=native -mtune=native -O3
export CFLAGS

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.
dist/libp256.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

HASH_BUNDLE= \
  -bundle Hacl.Impl.SHA2.Types=[rename=Hacl_SHA2_Types] \
  -static-header Hacl.Impl.SHA2.Generic \
  -bundle Hacl.Streaming.SHA2=Hacl.Hash.SHA2,Hacl.Hash.Core.SHA2,Hacl.Impl.SHA2.*,Hacl.SHA2.Scalar32[rename=Hacl_Hash_SHA2] \
  -bundle Hacl.Hash.Definitions=Hacl.Hash.*[rename=Hacl_Hash_Base]

dist/Makefile.basic: $(filter-out %prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o libp256.a \
	$(BASE_FLAGS) $(HASH_BUNDLE) $(STREAMING_BUNDLE) \
	$(BIGNUM_BUNDLE) $(P256_BUNDLE) \
	-tmpdir dist \
	-add-include '"lib_intrinsics.h"' \
	-no-prefix 'Hacl.Test.ECDSA' \
	-fbuiltin-uint128 \
	-skip-compilation

dist/p256-test.exe: dist/libp256.a \
	$(KRML_HOME)/krmllib/dist/generic/libkrmllib.a

%.exe:
	$(CC) $(CFLAGS) $^ -o $@

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
