HACL_HOME=$(realpath ../..)

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: \
	dist/aes128-bitslice-test.exe \
	dist/aes128-ni-test.exe

test: all
	dist/aes128-bitslice-test.exe
	dist/aes128-ni-test.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include $(HACL_HOME)/Makefile.local

#BASE_FLAGS+= -funroll-loops 4

CFLAGS += -I$(HACL_HOME)/lib/c -maes -mpclmul -msse4.1 -O3
#CFLAGS += -I../../../lib/c -march=native -mtune=native -O3
export CFLAGS

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.
dist/libaes.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o libaes.a $(BASE_FLAGS) $(AES_BUNDLE) \
	  -tmpdir dist -dast \
	  -add-include '"libintvector.h"' \
	  -skip-compilation

dist/aes128-bitslice-test.exe: $(HACL_HOME)/tests/aes128-bitslice-test.c dist/libaes.a
dist/aes256-bitslice-test.exe: $(HACL_HOME)/tests/aes256-bitslice-test.c dist/libaes.a
dist/aes128-ni-test.exe: $(HACL_HOME)/tests/aes128-ni-test.c dist/libaes.a
dist/aes256-ni-test.exe: $(HACL_HOME)/tests/aes256-ni-test.c dist/libaes.a

%.exe:
	$(CC) $(CFLAGS) -flto $^ -o $@

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
