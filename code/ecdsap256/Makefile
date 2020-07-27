HACL_HOME=../..

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).

CC = gcc-9.1
all: dist/Hacl_Test_ECDSA.exe

test: all
	dist/Hacl_Test_ECDSA.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include ../../Makefile.local

FSTAR_ROOTS += Hacl.Impl.P256.PointDouble.fst
# P256_BUNDLE=-bundle Hacl.Impl.P256.PointDouble=Hacl.Impl.ECDSA.*,Hacl.Impl.SolinasReduction,Hacl.Impl.P256.*

#BASE_FLAGS+= -funroll-loops 4

CFLAGS += -I ../../../lib/c -I . -march=native -mtune=native -O3
export CFLAGS

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

dist/Hacl_Test_ECDSA.exe: dist/Hacl_P256.o dist/Hacl_Test_ECDSA.o \
	$(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a dist/libecdsa.a


dist/p256-openssl-test.exe: dist/Hacl_P256.o
	$(CC) $(CFLAGS) -I $(OPENSSL_HOME)/include -I ../../dist/gcc64-only  -I $(OPENSSL_HOME)/include/crypto -I $(OPENSSL_HOME)/crypto \
	 $(HACL_HOME)/tests/p256-test.c $^ \
	-o $@ $(OPENSSL_HOME)/libcrypto.a -lpthread -ldl

%.exe:
	$(CC) $(CFLAGS) -flto $^ -o $@

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean


