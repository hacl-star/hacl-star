HACL_HOME=$(realpath ../..)

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: \
	dist/aes128-ctr32-ni-test.exe

test: all
	dist/aes128-ctr32-ni-test.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include $(HACL_HOME)/Makefile.local
include $(HACL_HOME)/dist/gcc-compatible/Makefile.config

CFLAGS += -I$(HACL_HOME)/lib/c $(CFLAGS_AESNI) -O3
export CFLAGS

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.
dist/libaes.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o libaes.a $(BASE_FLAGS) $(AES_CTR32_BUNDLE) \
	  -tmpdir dist -dast \
	  -add-include '"libintvector.h"' \
	  -skip-compilation

dist/aes128-ctr32-ni-test.exe: $(HACL_HOME)/tests/aes128-ctr32-ni-test.c dist/libaes.a

%.exe:
	$(CC) $(CFLAGS) -flto $^ -o $@

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
