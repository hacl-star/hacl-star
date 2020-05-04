HACL_HOME=../..

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: dist/sha2-vec-test.exe

test: all
	dist/sha2-vec-test.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include ../../Makefile.local

BASE_FLAGS+= -funroll-loops 5

CFLAGS += -I../../../lib/c -I../../lib/c -I ../hash/dist -march=native -mtune=native -O3
export CFLAGS

BLACKLIST += Hacl_SHA2_Vec512.c Hacl_SHA2_Vec512.h
export BLACKLIST

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.
dist/libsha2vec.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o libsha2vec.a $(BASE_FLAGS) $(SHA2VEC_BUNDLE) \
	  -add-include '"libintvector.h"' \
	  -tmpdir dist \
	  -skip-compilation

$(HACL_HOME)/tests/tests-openssl/sha256-mb/sha256-mb-x86_64.o: $(HACL_HOME)/tests/tests-openssl/sha256-mb/sha256-mb-x86_64.s
	$(CC) -c $(HACL_HOME)/tests/tests-openssl/sha256-mb/sha256-mb-x86_64.s -o $@

dist/sha2-mb-test.exe: $(HACL_HOME)/tests/tests-openssl/sha256-mb/sha256-mb-x86_64.o dist/libsha2vec.a
	$(CC) $(CFLAGS) -I $(HACL_HOME)/tests/tests-openssl/sha2-mb -I $(HACL_HOME)/tests \
	$(HACL_HOME)/tests/tests-openssl/sha256-mb/hash_simd.c $(HACL_HOME)/tests/tests-openssl/sha2-vec-test.c $^ \
	-o $@ -lcrypto


dist/sha2-vec-test.exe: $(HACL_HOME)/tests/sha2-vec-test.o dist/libsha2vec.a

%.exe:
	$(CC) $(CFLAGS) $^ -o $@ -lcrypto

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
