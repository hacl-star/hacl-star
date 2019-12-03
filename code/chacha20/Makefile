HACL_HOME=../..

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: dist/chacha20-test.exe dist/chacha20-vec-test.exe

test: all
	dist/chacha20-test.exe
	dist/chacha20-vec-test.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include ../../Makefile.local

CFLAGS += -I../../../lib/c -mavx -mavx2 -march=native -mtune=native -O3
export CFLAGS

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.
dist/libchacha.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic

dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o libchacha.a $(BASE_FLAGS) $(CHACHA20_BUNDLE) \
	  -tmpdir dist \
	  -add-include '"libintvector.h"' \
	  -skip-compilation

dist/chacha20-test.exe: $(HACL_HOME)/tests/chacha20-test.o dist/libchacha.a

dist/chacha20-vec-test.exe: $(HACL_HOME)/tests/chacha20-vec-test.o dist/libchacha.a

dist/chacha20-vec-openssl-test.exe: dist/libchacha.a
	$(CC) $(CFLAGS) -I $(OPENSSL_HOME)/include/crypto -I $(OPENSSL_HOME)/crypto $(HACL_HOME)/tests/tests-openssl/chacha20-vec-test.c $^ \
	$(KREMLIB_A) -o $@ $(OPENSSL_HOME)/libcrypto.a -lpthread -ldl

%.exe:
	$(CC) $(CFLAGS) -flto $^ $(KREMLIB_A) -o $@

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
