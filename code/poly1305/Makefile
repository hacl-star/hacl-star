HACL_HOME=../..

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: dist/poly1305-test.exe

test: all
	dist/poly1305-test.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include ../../Makefile.local

CFLAGS += -I../../../lib/c -march=native -mtune=native -O3
export CFLAGS

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.
dist/libpoly.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

# Note: POLY_BUNDLE is found in Makefile.common -- shared definition.
dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o libpoly.a $(BASE_FLAGS) $(POLY_BUNDLE) \
	  -tmpdir dist \
	  -add-include '"libintvector.h"' \
	  -add-include '<stdbool.h>' \
	  -skip-compilation

dist/poly1305-test.exe: $(HACL_HOME)/tests/poly1305-test.o dist/libpoly.a

dist/poly1305-openssl-test.exe: dist/libpoly.a
	$(CC) $(CFLAGS) -I $(OPENSSL_HOME)/include/crypto -I $(OPENSSL_HOME)/crypto -I $(HACL_HOME)/tests/tests-openssl/jasmin-poly-avx2 \
	$(HACL_HOME)/tests/tests-openssl/jasmin-poly-avx2/poly1305.s $(HACL_HOME)/tests/tests-openssl/poly1305-test.c $^ \
	-o $@ $(OPENSSL_HOME)/libcrypto.a -lpthread -ldl


%.exe:
	$(CC) $(CFLAGS) -flto $^ -o $@

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
