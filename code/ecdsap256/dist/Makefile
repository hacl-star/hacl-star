HACL_HOME=../..

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).

CC = gcc-9.1
all: dist/Hacl_Test_ECDSA.exe

dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o libecdsa.a $(BASE_FLAGS) $(P256_BUNDLE) \
	  -tmpdir dist \
	  -fbuiltin-uint128 \
	  -funroll-loops 12 \
	  -add-include '"lib_intrinsics.h"' \
	  -no-prefix 'Hacl.Test.ECDSA' \
	  -skip-compilation

# An archive with all the compiled code in this directory.
# We don't want Hacl_Test_ECDSA.o to be included so we redefine OBJS
dist/libecdsa.a:dist/Hacl_P256.o
	$(MAKE) -C dist -f Makefile.basic OBJS=$(notdir $^) $(notdir $@)
	
dist/%.o: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic $(notdir $@)

test.exe: Hacl_P256.o
	$(CC) $(CFLAGS) \
	test.c  $^ \
	-o test.exe

%.exe:
	$(CC) $(CFLAGS) -flto $^ -o $@

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean


