HACL_HOME=$(realpath ../..)

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: dist/rsa-test.exe

test: all
	dist/rsa-test.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include $(HACL_HOME)/Makefile.local

CFLAGS += -I$(HACL_HOME)/lib/c -march=native -mtune=native -O3 -DCOMPILE_INTRINSICS
export CFLAGS

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.
dist/librsa.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

SHA2_BUNDLE=-bundle Hacl.Hash.SHA2=Hacl.Hash.*
BIGNUM_BUNDLE= -bundle Hacl.Bignum.Base -static-header Hacl.Bignum.Base \
	-bundle Hacl.Bignum,Hacl.Bignum.*[rename=Hacl_Bignum]
RSA_BUNDLE=-bundle Hacl.RSA=Hacl.Impl.RSA.*,Hacl.Impl.RSA[rename=Hacl_RSA]

dist/Makefile.basic: $(filter-out %prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o librsa.a $(BASE_FLAGS) $(SHA2_BUNDLE) $(BIGNUM_BUNDLE) $(RSA_BUNDLE) \
	-tmpdir dist \
	-add-include '"lib_intrinsics.h"' \
	-fbuiltin-uint128 \
	-skip-compilation

dist/rsa-test.exe: $(HACL_HOME)/tests/rsa-test.o dist/librsa.a

%.exe:
	$(CC) $(CFLAGS) $^ -o $@

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
