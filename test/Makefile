include ../Makefile.include

GFIND=$(shell which gfind >/dev/null 2>&1 && echo gfind || echo find)
ifeq ($(OS),Windows_NT)
  GCC=x86_64-w64-mingw32-gcc.exe
  ENABLE_LTO=
else
  GCC=$(shell which gcc-7 >/dev/null 2>&1 && echo gcc-7 || (which gcc-6 >/dev/null 2>&1 && echo gcc-6 || echo gcc))
  ENABLE_LTO=-flto
endif
GCC_OPTS=$(ENABLE_LTO) -std=c11 -D_GNU_SOURCE

TWEETNACL_HOME ?= $(HACL_HOME)/other_providers/tweetnacl
OPENSSL_HOME   ?= $(HACL_HOME)/other_providers/openssl
LIBSODIUM_HOME ?= $(HACL_HOME)/other_providers/libsodium/src/libsodium

# Default snapshot. Variable can be overwritten to choose a snapshot
SNAPSHOT_DIR = snapshots/hacl-c

#
# Compiler and settings
#

CCOPTS = -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops
CFLAGS = $(CCOPTS) -I $(OPENSSL_HOME) -I $(OPENSSL_HOME)/include -I $(OPENSSL_HOME)/crypto/ec \
	-I $(OPENSSL_HOME)/crypto/include -I $(OPENSSL_HOME)/crypto/poly1305 \
	-I $(LIBSODIUM_HOME)/include -L$(LIBSODIUM_HOME)/lib \
	-I $(TWEETNACL_HOME) -I .

CC_BASE = $(CC) $(CFLAGS) -I $(HACL_HOME)/$(SNAPSHOT_DIR) -I ./c $(ADDITIONAL_FILES) \
	c/hacl_test_utils.c $(TWEETNACL_HOME)/tweetnacl.c $(HACL_HOME)/$(SNAPSHOT_DIR)/kremlib.c $(HACL_HOME)/$(SNAPSHOT_DIR)/testlib.c 

PERF_LIBS=$(OPENSSL_HOME)/libcrypto.a -lsodium -lpthread -ldl

CCOMP?=ccomp
FSTARH_CCOMP=$(HACL_HOME)/snapshots/snapshot-ccomp/FStar.c
CCOMP_OPTS=-O3 -DKRML_NOUINT128 -DKRML_NOSTRUCT_PASSING -finline-asm -D_BSD_SOURCE -D_DEFAULT_SOURCE

#
# Unit tests
#

all: test-specs test-code test-vale test-vale-asm all-unit-tests all-unit-tests-32
	$(MAKE) test-perf-all
	#$(MAKE) test-pneutube
	#$(MAKE) -C openssl-engine
	#$(MAKE) test-snapshot
	#$(MAKE) test-ccomp
	#$(MAKE) test-gcc
	#$(MAKE) test-gcc-unrolled

#
# Tests for the specs
#

test-specs:
	$(MAKE) -C ../specs


#
# Tests for code
#

test-code:
	$(MAKE) -C ../code test

#
# Tests for Vale
#

test-vale:
	$(MAKE) -C ../secure_api krml-test-vale.exe
	$(MAKE) -C ../secure_api krml-test-hacl.exe

test-vale-asm:
	$(MAKE) -C ../secure_api/vale/asm/

#
# Tests for applications
#

test-pneutube:
	$(MAKE) -C ../apps/pneutube tube-star.exe

#
# Building snapshots
#

.snapshot-all:
	$(MAKE) -C .. snapshots-all

#
# Standalone unit-tests
#

# 64-bit unit tests
unit-tests:
	$(MAKE) -C $(HACL_HOME)/$(SNAPSHOT_DIR) libnacl.so
ifeq ($(SNAPSHOT_DIR),snapshots/snapshot-ccomp)
	$(CCOMP) $(CCOMP_OPTS) $(FSTARH_CCOMP) -I $(HACL_HOME)/$(SNAPSHOT_DIR) -I $(HACL_HOME)/snapshots/c -I c/ -I $(TWEETNACL_HOME) \
		$(TWEETNACL_HOME)/tweetnacl.c c/hacl_test_utils.c c/unit_tests.c $(HACL_HOME)/$(SNAPSHOT_DIR)/libnacl.so -o unit_tests.exe
else
	$(CC) $(CCOPTS) -I $(HACL_HOME)/$(SNAPSHOT_DIR) -I $(HACL_HOME)/snapshots/c -I c/ -I $(TWEETNACL_HOME) \
		$(TWEETNACL_HOME)/tweetnacl.c c/hacl_test_utils.c c/unit_tests.c $(HACL_HOME)/$(SNAPSHOT_DIR)/libnacl.so -o unit_tests.exe
endif
	LD_LIBRARY_PATH=$(HACL_HOME)/$(SNAPSHOT_DIR) DYLD_LIBRARY_PATH=$(HACL_HOME)/$(SNAPSHOT_DIR) ./unit_tests.exe

# 32-bit unit tests
unit-tests-32:
	$(MAKE) -C .. build/libhacl32.so
ifeq ($(SNAPSHOT_DIR),snapshots/snapshot-ccomp)
	$(CCOMP) $(CCOMP_OPTS) $(FSTARH_CCOMP) -I $(HACL_HOME)/$(SNAPSHOT_DIR) -I ../snapshots/c -I c/ -I $(TWEETNACL_HOME) \
		$(TWEETNACL_HOME)/tweetnacl.c c/hacl_test_utils.c c/unit_tests.c $(HACL_HOME)/build/libnacl32.so -o unit_tests32.exe
else
	$(CC) $(CFLAGS) -DKRML_NOUINT128  -I $(HACL_HOME)/$(SNAPSHOT_DIR) -I ../snapshots/c -I c/ -I $(TWEETNACL_HOME) \
		$(TWEETNACL_HOME)/tweetnacl.c c/hacl_test_utils.c c/unit_tests.c $(HACL_HOME)/build/libnacl32.so -o unit_tests32.exe
endif
	LD_LIBRARY_PATH=$(HACL_HOME)/build DYLD_LIBRARY_PATH=$(HACL_HOME)/build ./unit_tests32.exe

unit-tests-hacl-c:
	$(MAKE) unit-tests SNAPSHOT_DIR=snapshots/hacl-c

unit-tests-gcc:
	$(MAKE) unit-tests SNAPSHOT_DIR=snapshots/snapshot-gcc

unit-tests-gcc-unrolled:
	$(MAKE) unit-tests SNAPSHOT_DIR=snapshots/snapshot-gcc-unrolled

unit-tests-ccomp:
	$(MAKE) unit-tests CC=$(CCOMP) CCOPTS="$(CCOMP_OPTS)" ADDITIONAL_FILES=$(FSTARH_CCOMP) SNAPSHOT_DIR=snapshots/snapshot-ccomp

# # FIXME: setup tests for MSVC
# unit-tests-msvc:
# 	$(MAKE) unit-tests SNAPSHOT_DIR=snapshots/snapshot-msvc

all-unit-tests:
	$(MAKE) unit-tests-hacl-c
	$(MAKE) unit-tests-gcc
	$(MAKE) unit-tests-gcc-unrolled
	# JK: FIXME, run unit-tests from CompCert
	# $(MAKE) unit-tests-ccomp
	# $(MAKE) unit-tests-msvc


unit-tests-32-hacl-c:
	$(MAKE) unit-tests-32 SNAPSHOT_DIR=snapshots/hacl-c

unit-tests-32-gcc:
	$(MAKE) unit-tests-32 SNAPSHOT_DIR=snapshots/snapshot-gcc

unit-tests-32-gcc-unrolled:
	$(MAKE) unit-tests-32 SNAPSHOT_DIR=snapshots/snapshot-gcc-unrolled

unit-tests-32-ccomp:
	$(MAKE) unit-tests-32 CC=$(CCOMP) CCOPTS="$(CCOMP_OPTS)" ADDITIONAL_FILES=$(FSTARH_CCOMP) SNAPSHOT_DIR=snapshots/snapshot-ccomp

# # FIXME: setup tests for MSVC
# unit-tests-32-msvc:
# 	$(MAKE) unit-tests-32 SNAPSHOT_DIR=snapshots/snapshot-msvc

all-unit-tests-32:
	$(MAKE) unit-tests-32-hacl-c
	$(MAKE) unit-tests-32-gcc
	$(MAKE) unit-tests-32-gcc-unrolled
	$(MAKE) unit-tests-32-ccomp
	# $(MAKE) unit-tests-32-msvc

#
# Tests for Poly1305
#

test-poly1305.exe:
	$(CC_BASE) $(HACL_HOME)/$(SNAPSHOT_DIR)/Poly1305_64.c c/test-poly.c -o test-poly1305.exe \
		$(PERF_LIBS)

test-unit-poly1305: test-poly1305.exe
	./test-poly1305.exe unit-test

test-perf-poly1305: test-poly1305.exe
	./test-poly1305.exe perf

#
# Tests for Salsa20
#

test-salsa20.exe:
	$(CC_BASE) $(HACL_HOME)/$(SNAPSHOT_DIR)/Salsa20.c c/test-salsa.c -o test-salsa20.exe $(PERF_LIBS)

test-unit-salsa20: test-salsa20.exe
	./test-salsa20.exe unit-test

test-perf-salsa20: test-salsa20.exe
	./test-salsa20.exe perf

#
# Tests for Chacha20
#

test-chacha20.exe:
	$(CC_BASE) $(HACL_HOME)/$(SNAPSHOT_DIR)/Chacha20.c c/test-chacha.c -o test-chacha20.exe $(PERF_LIBS)

test-unit-chacha20: test-chacha20.exe
	./test-chacha20.exe unit-test

test-perf-chacha20: test-chacha20.exe
	./test-chacha20.exe perf

#
# Tests for Chacha20 (Vectorized over 128bit)
#

define EMPTY_SCRIPT
#!/bin/bash
echo No vectors with CompCert
endef
export EMPTY_SCRIPT

test-chacha20-vec128.exe:
ifeq ($(CC),ccomp)
	@echo "Skipping tests for vectorized chacha20 as CompCert does not support it"
	@echo "$$EMPTY_SCRIPT" > test-chacha20-vec128.exe
	@chmod +x test-chacha20-vec128.exe
else
	$(CC_BASE) -lpthread $(LIBDL) $(LIBWINSOCK) $(HACL_HOME)/$(SNAPSHOT_DIR)/Chacha20_Vec128.c c/test-chacha-vec128.c -o test-chacha20-vec128.exe $(PERF_LIBS)
endif

test-unit-chacha20-vec128: test-chacha20-vec128.exe
ifeq ($(CC),ccomp)
	@echo "No performance tests for vectorized chacha20 with CompCert"
else
	./test-chacha20-vec128.exe unit-test
endif

test-perf-chacha20-vec128: test-chacha20-vec128.exe
ifeq ($(CC),ccomp)
	@echo "No unit tests for vectorized chacha20 with CompCert"
else
	./test-chacha20-vec128.exe perf
endif

#
# Tests for Curve25519 (64bit)
#

test-curve25519.exe:
	$(CC_BASE) -lpthread $(LIBDL) $(HACL_HOME)/$(SNAPSHOT_DIR)/Curve25519.c c/test-curve.c -o test-curve25519.exe $(PERF_LIBS)

test-unit-curve25519: test-curve25519.exe
	./test-curve25519.exe unit-test

test-perf-curve25519: test-curve25519.exe
	./test-curve25519.exe perf

#
# Tests for SHA2_512
#

test-sha512.exe:
	$(CC_BASE) -lpthread $(LIBDL) $(HACL_HOME)/$(SNAPSHOT_DIR)/SHA2_512.c c/test-sha512.c -o test-sha512.exe $(PERF_LIBS)

test-unit-sha512: test-sha512.exe
	./test-sha512.exe unit-test

test-perf-sha512: test-sha512.exe
	./test-sha512.exe perf

#
# Tests for Ed25519
#

test-ed25519.exe:
	$(CC_BASE) -lpthread $(LIBDL) $(HACL_HOME)/$(SNAPSHOT_DIR)/SHA2_512.c $(HACL_HOME)/$(SNAPSHOT_DIR)/Ed25519.c c/test-ed25519.c -o test-ed25519.exe $(PERF_LIBS)

test-unit-ed25519: test-ed25519.exe
	./test-ed25519.exe unit-test

test-perf-ed25519: test-ed25519.exe
	./test-ed25519.exe perf

#
# Tests for the SecretBox API
#

test-secretbox.exe:
	$(CC) $(CFLAGS) -c $(HACL_HOME)/$(SNAPSHOT_DIR)/Salsa20.c     -o Salsa20.o
	$(CC) $(CFLAGS) -c $(HACL_HOME)/$(SNAPSHOT_DIR)/Poly1305_64.c -o Poly1305_64.o
	$(CC) $(CFLAGS) -c $(HACL_HOME)/$(SNAPSHOT_DIR)/Curve25519.c  -o Curve25519.o
	$(CC_BASE) Salsa20.o Poly1305_64.o Curve25519.o \
		$(HACL_HOME)/$(SNAPSHOT_DIR)/Hacl_Policies.c $(HACL_HOME)/$(SNAPSHOT_DIR)/NaCl.c c/test-secretbox.c -o test-secretbox.exe $(PERF_LIBS)

test-unit-secretbox: test-secretbox.exe
	./test-secretbox.exe unit-test

test-perf-secretbox: test-secretbox.exe
	./test-secretbox.exe perf

#
# Test for the Box API
#

test-box.exe:
	$(CC) $(CFLAGS) -c $(HACL_HOME)/$(SNAPSHOT_DIR)/Salsa20.c     -o Salsa20.o
	$(CC) $(CFLAGS) -c $(HACL_HOME)/$(SNAPSHOT_DIR)/Poly1305_64.c -o Poly1305_64.o
	$(CC) $(CFLAGS) -c $(HACL_HOME)/$(SNAPSHOT_DIR)/Curve25519.c  -o Curve25519.o
	$(CC_BASE) Salsa20.o Poly1305_64.o Curve25519.o \
		$(HACL_HOME)/$(SNAPSHOT_DIR)/Hacl_Policies.c $(HACL_HOME)/$(SNAPSHOT_DIR)/NaCl.c c/test-box.c -o test-box.exe $(PERF_LIBS)

test-unit-box: test-box.exe
	./test-box.exe unit-test

test-perf-box: test-box.exe
	./test-box.exe perf

#
# Tests for the AEAD API
#

test-aead.exe:
	$(CC) $(CFLAGS) -c $(HACL_HOME)/$(SNAPSHOT_DIR)/Chacha20.c         -o Chacha20.o
	$(CC) $(CFLAGS) -c $(HACL_HOME)/$(SNAPSHOT_DIR)/AEAD_Poly1305_64.c -o AEAD_Poly1305_64.o
	$(CC_BASE) -lpthread $(LIBDL) $(LIBWINSOCK) Chacha20.o AEAD_Poly1305_64.o \
		$(HACL_HOME)/$(SNAPSHOT_DIR)/Hacl_Policies.c $(HACL_HOME)/$(SNAPSHOT_DIR)/Chacha20Poly1305.c c/test-aead.c -o test-aead.exe $(PERF_LIBS)

test-unit-aead: test-aead.exe
	./test-aead.exe unit-test

test-perf-aead: test-aead.exe
	./test-aead.exe perf

#
# Targets for all primitives
#

test-unit-all: test-unit-poly1305 test-unit-chacha20 test-unit-chacha20-vec128 test-unit-salsa20 test-unit-curve25519 test-unit-secretbox test-unit-box test-unit-aead test-unit-ed25519 # test-unit-sha512

test-perf-all: test-perf-poly1305 test-perf-chacha20 test-perf-salsa20 test-perf-curve25519 test-perf-secretbox test-perf-box test-perf-aead test-perf-ed25519 # test-perf-chacha20-vec128 test-perf-sha512

test-all-%: .snapshot-all
	$(MAKE) CC="$(GCC) $(GCC_OPTS)" SNAPSHOT_DIR="snapshots/hacl-c" test-$*.exe && ./test-$*.exe
	@rm test-$*.exe
	$(MAKE) CC="$(GCC) $(GCC_OPTS)" SNAPSHOT_DIR="snapshots/snapshot-gcc" test-$*.exe && ./test-$*.exe
	@rm test-$*.exe
	$(MAKE) CC="$(GCC) $(GCC_OPTS)" SNAPSHOT_DIR="snapshots/snapshot-gcc-unrolled" test-$*.exe && ./test-$*.exe
	@rm test-$*.exe
	$(MAKE) CC="ccomp" CCOPTS="$(CCOMP_OPTS)" ADDITIONAL_FILES=$(FSTARH_CCOMP) SNAPSHOT_DIR="snapshots/snapshot-ccomp" test-$*.exe && ./test-$*.exe
	@rm test-$*.exe
#	$(MAKE) CC="$(MSVC) $(MSVC_OPTS)" SNAPSHOT_DIR="snapshots/snapshot-msvc" test-poly.exe; ./test-$*.exe

test-all-perf: $(addprefix test-all-, poly1305 chacha20 chacha20-vec128 salsa20 curve25519 secretbox box aead ed25519 sha512)

#
# Additionnal targets
#

clean:
	rm -rf *~ *.o *.exe


# lib:
# 	$(CC) $(CFLAGS) \
# 	  Salsa20.c -c -o Salsa20.o
# 	$(CC) $(CFLAGS) \
# 	  Chacha20.c -c -o Chacha20.o
# 	$(CC) $(CFLAGS) \
# 	  Poly1305_64.c -c -o Poly1305_64.o
# 	$(CC) $(CFLAGS) \
# 	  AEAD_Poly1305_64.c -c -o AEAD_Poly1305_64.o
# 	$(CC) $(CFLAGS) \
# 	  SHA2_512.c -c -o SHA2_512.o
# 	$(CC) $(CFLAGS) \
# 	  Ed25519.c -c -o Ed25519.o
# 	$(CC) $(CFLAGS) \
# 	  Curve25519.c -c -o Curve25519.o
# 	$(CC) $(CFLAGS) \
# 	  Chacha20Poly1305.c -c -o Chacha20Poly1305.o
# 	$(CC) -shared  $(CFLAGS) \
# 	  Salsa20.o Poly1305_64.o Chacha20.o AEAD_Poly1305_64.o Chacha20Poly1305.o SHA2_512.o Ed25519.o Curve25519.o kremlib.c Hacl_Policies.c NaCl.c \
# 	  -o libhacl.so

# lib-test: lib
# 	$(CC)  $(CFLAGS) \
# 	  -I $(OPENSSL_HOME)/crypto/include -I $(OPENSSL_HOME)/crypto/poly1305 \
# 	  hacl_test_utils.c \
# 	  -I $(TWEETNACL_HOME) $(TWEETNACL_HOME)/tweetnacl.c \
# 	  testlib.c test-poly.c -o test-poly.exe \
# 	  -lsodium $(OPENSSL_HOME)/libcrypto.a libhacl.so
# 	$(CC)  $(CFLAGS) \
# 	  hacl_test_utils.c \
# 	  -I $(TWEETNACL_HOME) $(TWEETNACL_HOME)/tweetnacl.c \
# 	  testlib.c test-salsa.c -o test-salsa.exe \
# 	  -lsodium $(OPENSSL_HOME)/libcrypto.a libhacl.so
# 	$(CC)  $(CFLAGS) \
# 	  -I $(OPENSSL_HOME)/include -I $(OPENSSL_HOME)/crypto/poly1305 -I ../../other_providers/tweetnacl \
# 	  hacl_test_utils.c \
# 	  ../../other_providers/tweetnacl/tweetnacl.c testlib.c test-chacha.c -o test-chacha.exe \
# 	   $(OPENSSL_HOME)/libcrypto.a -lsodium -lpthread $(LIBDL) libhacl.so
# 	$(CC)  $(CFLAGS) \
# 	  hacl_test_utils.c \
# 	  -I $(TWEETNACL_HOME) $(TWEETNACL_HOME)/tweetnacl.c \
# 	  testlib.c test-secretbox.c -o test-secretbox.exe \
# 	  -lsodium $(OPENSSL_HOME)/libcrypto.a libhacl.so
# 	$(CC)  $(CFLAGS) \
# 	  testlib.c hacl_test_utils.c test-aead.c -o test-aead.exe \
# 	  -lsodium  $(OPENSSL_HOME)/libcrypto.a $(OPENSSL_HOME)/libssl.a -lpthread $(LIBDL) libhacl.so
# 	$(CC)  $(CFLAGS) \
# 	  -I $(OPENSSL_HOME) -I $(OPENSSL_HOME)/include -I $(OPENSSL_HOME)/crypto/ec \
# 	  hacl_test_utils.c \
# 	  -I $(TWEETNACL_HOME) $(TWEETNACL_HOME)/tweetnacl.c \
# 	  testlib.c test-curve.c -o test-curve.exe \
# 	  $(OPENSSL_HOME)/libcrypto.a $(OPENSSL_HOME)/libssl.a -lsodium -lpthread $(LIBDL) libhacl.so
# 	$(CC)  $(CFLAGS) \
# 	  hacl_test_utils.c \
# 	  -I $(TWEETNACL_HOME) $(TWEETNACL_HOME)/tweetnacl.c \
# 	  testlib.c test-box.c -o test-box.exe -lsodium  libhacl.so
# 	./test-chacha.exe
# 	./test-salsa.exe
# 	./test-poly.exe
# 	./test-secretbox.exe
# 	./test-aead.exe
# 	./test-curve.exe
# 	./test-box.exe


# test-snapshot-hacl-c:
# 	$(MAKE) -C .. snapshots/snapshot-hacl
# 	$(MAKE) -C ../snapshots/snapshot-hacl CC="$(GCC) $(GCC_OPTS)" test

# test-snapshot-ccomp:
# 	$(MAKE) -C .. snapshots/snapshot-ccomp
# 	$(MAKE) -C ../snapshots/snapshot-ccomp CC=ccomp CCOPTS="-O3 -DKRML_NOUINT128 -DKRML_NOSTRUCT_PASSING -finline-asm -D_BSD_SOURCE -D_DEFAULT_SOURCE" test

# test-snapshot-gcc:
# 	$(MAKE) -C .. snapshots/snapshot-gcc
# 	$(MAKE) -C ../snapshots/snapshot-gcc CC="$(GCC) -fno-tree-vectorize $(ENABLE_LTO)" CCOPTS="-Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops " test

# test-snapshot-gcc-unrolled:
# 	$(MAKE) -C .. snapshots/snapshot-gcc-unrolled
# 	$(MAKE) -C ../snapshots/snapshot-gcc-unrolled CC="$(GCC) -fno-tree-vectorize $(ENABLE_LTO)" CCOPTS="-Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops " test

#
# Performance tests
#

# echo-perf-ccomp:
# 	$(shell (echo -e "Benchmarking results with ccomp -O3 -DKRML_NOUINT128 -DKRML_NOSTRUCT_PASSING -finline-asm -D_BSD_SOURCE -D_DEFAULT_SOURCE\n\nAlgorithm       HACL(cy/b)      LibSodium(cy/b) OpenSSL(cy/b)   TweetNaCl(cy/b) HACL(us/b)      LibSodium(us/b) OpenSSL(us/b)   TweetNaCl(us/b) \n"; cat $(HACL_HOME)/snapshot-ccomp/bench.txt) > benchmark-compcert.txt)

# perf-ccomp:
# 	-$(MAKE) -B -C $(HACL_HOME)/snapshots/snapshot-ccomp CC=ccomp CCOPTS="-O3 -DKRML_NOUINT128 -DKRML_NOSTRUCT_PASSING -finline-asm -D_BSD_SOURCE -D_DEFAULT_SOURCE" perf
# 	$(MAKE) -B echo-perf-ccomp

# echo-perf-gcc:
# 	$(shell (echo -e "Benchmarking results with $(GCC) -fno-tree-vectorize $(ENABLE_LTO) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops\n\nAlgorithm       HACL(cy/b)      LibSodium(cy/b) OpenSSL(cy/b)   TweetNaCl(cy/b) HACL(us/b)      LibSodium(us/b) OpenSSL(us/b)   TweetNaCl(us/b) \n"; cat snapshot-gcc/bench.txt) > benchmark-gcc.txt)

# perf-gcc:
# 	$(MAKE) -B -C snapshot-gcc CC="$(GCC) -fno-tree-vectorize $(ENABLE_LTO)" CCOPTS="-Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops " perf
# 	$(MAKE) -B echo-perf-gcc

# echo-gcc-unrolled:
# 	$(shell (echo -e "Benchmarking results with $(GCC) -fno-tree-vectorize $(ENABLE_LTO) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops with KreMLin loop unrolling\n\nAlgorithm       HACL(cy/b)      LibSodium(cy/b) OpenSSL(cy/b)   TweetNaCl(cy/b) HACL(us/b)      LibSodium(us/b) OpenSSL(us/b)   TweetNaCl(us/b) \n"; cat snapshot-gcc-unrolled/bench.txt) > benchmark-gcc-unrolled.txt)

# perf-gcc-unrolled:
# 	$(MAKE) -B -C snapshot-gcc-unrolled CC="$(GCC) -fno-tree-vectorize $(ENABLE_LTO)" CCOPTS="-Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops " perf
# 	$(MAKE) -B echo-gcc-unrolled

# all-perf:
# 	$(MAKE) perf-gcc
# 	$(MAKE) perf-gcc-unrolled
# 	$(MAKE) perf-ccomp
