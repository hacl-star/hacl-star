HACL_HOME=$(realpath ../..)

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: \
	dist/aesgcm-ni-test.exe \
	dist/aesgcm-m32-test.exe

test: all
	dist/aesgcm-ni-test.exe
	dist/aesgcm-m32-test.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include $(HACL_HOME)/Makefile.local

#BASE_FLAGS+= -funroll-loops 4

CFLAGS += -I$(HACL_HOME)/lib/c -maes -mpclmul -msse4.1 -O3
export CFLAGS

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.
dist/libaesgcm.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o libaesgcm.a $(BASE_FLAGS) $(AES_GCM_BUNDLE) \
	  -tmpdir dist -dast \
	  -add-include '"libintvector.h"' \
	  -skip-compilation

dist/aesgcm-ni-test.exe: $(HACL_HOME)/tests/aesgcm-ni-test.c dist/libaesgcm.a
dist/aesgcm-m32-test.exe: $(HACL_HOME)/tests/aesgcm-m32-test.c dist/libaesgcm.a

%.exe:
	$(CC) $(CFLAGS) -flto $^ -o $@

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
