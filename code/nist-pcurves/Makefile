HACL_HOME=$(realpath ../..)

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: dist/Makefile.basic

# Defines rules for producing .checked, .krml, .depend, etc.
include $(HACL_HOME)/Makefile.local

FSTAR_ROOTS = Hacl.P256.fst

CFLAGS += -I$(HACL_HOME)/lib/c -march=native -mtune=native -O3
export CFLAGS

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.
dist/libp256.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

dist/Makefile.basic: $(filter-out %prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o libp256.a \
	$(BASE_FLAGS) $(BIGNUM_BUNDLE) $(P256_BUNDLE) \
	$(notdir $(HAND_WRITTEN_FILES)) \
	-tmpdir dist \
	-add-include '"lib_intrinsics.h"' \
	-no-prefix 'Hacl.Test.ECDSA' \
	-fbuiltin-uint128 \
	-skip-compilation

%.exe:
	$(CC) $(CFLAGS) $^ -o $@

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
