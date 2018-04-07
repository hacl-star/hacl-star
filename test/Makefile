include ../Makefile.include

TWEETNACL_HOME ?= $(HACL_HOME)/other_providers/tweetnacl
OPENSSL_HOME   ?= $(HACL_HOME)/other_providers/openssl
LIBSODIUM_HOME ?= $(HACL_HOME)/other_providers/libsodium/src/libsodium

# Default snapshot. Variable can be overwritten to choose a snapshot
SNAPSHOT_DIR = snapshots/hacl-c

#
# Compiler and settings
#

CC = gcc-7
CCOPTS = -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops --param max-unroll-times=20
#CCOPTS = -Ofast -march=armv8-a+crc -mtune=cortex-a53 -mfpu=neon-fp-armv8 -fwrapv -fomit-frame-pointer -funroll-loops

CFLAGS = $(CCOPTS) -I $(OPENSSL_HOME) -I $(OPENSSL_HOME)/include -I $(OPENSSL_HOME)/crypto/ec \
	-I $(OPENSSL_HOME)/crypto/include -I $(OPENSSL_HOME)/crypto/poly1305 \
	-I $(LIBSODIUM_HOME)/include -L$(LIBSODIUM_HOME)/lib \
	-I $(TWEETNACL_HOME) -I . -I $(KREMLIB)

CC_BASE = $(CC) $(CFLAGS) -I $(HACL_HOME)/$(SNAPSHOT_DIR) -I ./test-files $(ADDITIONAL_FILES) \
	test-files/hacl_test_utils.c $(TWEETNACL_HOME)/tweetnacl.c $(KREMLIB)/kremlib.c $(KREMLIB)/testlib.c

PERF_LIBS=$(OPENSSL_HOME)/libcrypto.a -lsodium -lpthread -ldl

CCOMP?=ccomp
FSTARH_CCOMP=$(HACL_HOME)/snapshots/hacl-c-compcert/FStar.c
CCOMP_OPTS=-O3 -DKRML_NOUINT128 -DKRML_NOSTRUCT_PASSING -finline-asm -D_BSD_SOURCE -D_DEFAULT_SOURCE

#
# Unit tests
#

all:
	$(MAKE) test-code           # Previously 'make -C ../code test'
	$(MAKE) test-libhacl.so     # Previously 'make unit-tests' for 'hacl-c'
	$(MAKE) test-vale            # Previously not tested
	$(MAKE) test-vale-asm        # Previously 'make compile-vale'

# Improvements
# $(MAKE) test-libhacl32.so   # Previously 'make unit-tests' for 'hacl-c'
# $(MAKE) test-provider-lowc
# $(MAKE) -C openssl-engine
# $(MAKE) all-unit-tests
# $(MAKE) all-unit-tests-32
# $(MAKE) test-perf-all
# $(MAKE) test-pneutube        # Previously 'make extract-c-apps'

# Note
# 'extract-all-c' 'ct' 'verify-all' 'extract-specs' are now invoked at top-level

#
# Tests for specifications
#

test-specs:
	$(MAKE) -C ../specs clean
	$(MAKE) -C ../specs

#
# Tests for code
#

test-code:
	$(MAKE) -C ../code clean
	$(MAKE) -C ../code test

#
# Tests for shared libraries with cross-tests against TweetNacl
#

# 64-bit unit tests
test-snapshot-libhacl.so:
	$(MAKE) -C $(HACL_HOME)/$(SNAPSHOT_DIR) libhacl.so
	cp $(HACL_HOME)/$(SNAPSHOT_DIR)/libhacl.so .
ifeq ($(SNAPSHOT_DIR),snapshots/hacl-c-compcert)
	$(CCOMP) $(CCOMP_OPTS) $(FSTARH_CCOMP) \
		-I $(HACL_HOME)/$(SNAPSHOT_DIR) -I $(HACL_HOME)/snapshots/kremlib -I test-files/ -I $(TWEETNACL_HOME) \
		$(TWEETNACL_HOME)/tweetnacl.c test-files/hacl_test_utils.c test-files/unit_tests.c \
		libhacl.so -o unit_tests.exe
else
	$(CC) $(CCOPTS) \
		-I $(HACL_HOME)/$(SNAPSHOT_DIR) -I $(HACL_HOME)/snapshots/kremlib -I test-files/ -I $(TWEETNACL_HOME) \
		$(TWEETNACL_HOME)/tweetnacl.c test-files/hacl_test_utils.c test-files/unit_tests.c \
		libhacl.so -o unit_tests.exe
endif
ifeq ($(UNAME), Linux)
	LD_LIBRARY_PATH=.:$LD_LIBRARY_PATH ./unit_tests.exe
else
	./unit_tests.exe
endif
	rm libhacl.so

# 32-bit unit tests
test-snapshot-libhacl32.so:
	$(MAKE) -C $(HACL_HOME)/$(SNAPSHOT_DIR) libhacl32.so
	cp $(HACL_HOME)/$(SNAPSHOT_DIR)/libhacl32.so .
ifeq ($(SNAPSHOT_DIR),snapshots/hacl-c-compcert)
	$(CCOMP) $(CCOMP_OPTS) $(FSTARH_CCOMP) \
		-I $(HACL_HOME)/$(SNAPSHOT_DIR) -I ../snapshots/kremlib -I test-files/ -I $(TWEETNACL_HOME) \
		$(TWEETNACL_HOME)/tweetnacl.c test-files/hacl_test_utils.c test-files/unit_tests.c \
		libhacl32.so -o unit_tests32.exe
else
	$(CC) $(CFLAGS) -DKRML_NOUINT128  \
		-I $(HACL_HOME)/$(SNAPSHOT_DIR) -I ../snapshots/kremlib -I test-files/ -I $(TWEETNACL_HOME) \
		$(TWEETNACL_HOME)/tweetnacl.c test-files/hacl_test_utils.c test-files/unit_tests.c \
		libhacl32.so -o unit_tests32.exe
endif
ifeq ($(UNAME), Linux)
	LD_LIBRARY_PATH=.:$LD_LIBRARY_PATH ./unit_tests32.exe
else
	./unit_tests32.exe
endif
	rm libhacl32.so


test-snapshot-gcc-libhacl.so:
	$(MAKE) test-snapshot-libhacl.so SNAPSHOT_DIR=snapshots/snapshot-gcc

test-snapshot-gcc-unrolled-libhacl.so:
	$(MAKE) test-snapshot-libhacl.so SNAPSHOT_DIR=snapshots/snapshot-gcc-unrolled

test-hacl-c-libhacl.so:
	$(MAKE) test-snapshot-libhacl.so SNAPSHOT_DIR=snapshots/hacl-c

test-hacl-c-compcert:
	$(MAKE) test-snapshot-libhacl.so CC=$(CCOMP) CCOPTS="$(CCOMP_OPTS)" ADDITIONAL_FILES=$(FSTARH_CCOMP) SNAPSHOT_DIR=snapshots/hacl-c-compcert

test-snapshot-gcc-libhacl32.so:
	$(MAKE) test-snapshot-libhacl32.so SNAPSHOT_DIR=snapshots/snapshot-gcc

test-snapshot-gcc-unrolled-libhacl32.so:
	$(MAKE) test-snapshot-libhacl32.so SNAPSHOT_DIR=snapshots/snapshot-gcc-unrolled

test-hacl-c-libhacl32.so:
	$(MAKE) test-snapshot-libhacl32.so SNAPSHOT_DIR=snapshots/hacl-c

test-hacl-c-compcert:
	$(MAKE) test-snapshot-libhacl32.so CC=$(CCOMP) CCOPTS="$(CCOMP_OPTS)" ADDITIONAL_FILES=$(FSTARH_CCOMP) SNAPSHOT_DIR=snapshots/hacl-c-compcert

test-libhacl.so:
	$(MAKE) test-snapshot-gcc-libhacl.so
	$(MAKE) test-snapshot-gcc-unrolled-libhacl.so
	$(MAKE) test-hacl-c-libhacl.so
	$(MAKE) test-hacl-c-compcert-libhacl.so

test-libhacl32.so:
	$(MAKE) test-snapshot-gcc-libhacl32.so
	$(MAKE) test-snapshot-gcc-unrolled-libhacl32.so
	$(MAKE) test-hacl-c-libhacl32.so
	$(MAKE) test-hacl-c-compcert-libhacl32.so

#
# Building snapshots
#

.snapshot-all:
	$(MAKE) -C .. snapshots-all

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
	$(MAKE) CC="ccomp" CCOPTS="$(CCOMP_OPTS)" ADDITIONAL_FILES=$(FSTARH_CCOMP) SNAPSHOT_DIR="snapshots/hacl-c-compcert" test-$*.exe && ./test-$*.exe
	@rm test-$*.exe
#	$(MAKE) CC="$(MSVC) $(MSVC_OPTS)" SNAPSHOT_DIR="snapshots/snapshot-msvc" test-poly.exe; ./test-$*.exe

test-all-perf: $(addprefix test-all-, poly1305 chacha20 chacha20-vec128 salsa20 curve25519 secretbox box aead ed25519 sha512)

#
# Tests for Poly1305
#

test-poly1305.exe:
	$(CC_BASE) $(HACL_HOME)/$(SNAPSHOT_DIR)/Hacl_Poly1305_64.c test-files/test-poly.c -o test-poly1305.exe \
		$(PERF_LIBS)

test-poly1305-32.exe:
	$(CC_BASE) $(HACL_HOME)/$(SNAPSHOT_DIR)/Hacl_Poly1305_32.c test-files/test-poly32.c -o test-poly1305-32.exe \
		$(PERF_LIBS)

test-unit-poly1305: test-poly1305.exe
	./test-poly1305.exe unit-test

test-perf-poly1305: test-poly1305.exe
	./test-poly1305.exe perf

test-unit-poly1305-32: test-poly1305-32.exe
	./test-poly1305-32.exe unit-test

test-perf-poly1305-32: test-poly1305-32.exe
	./test-poly1305-32.exe perf

#
# Tests for Salsa20
#

test-salsa20.exe:
	$(CC_BASE) $(HACL_HOME)/$(SNAPSHOT_DIR)/Hacl_Salsa20.c test-files/test-salsa.c -o test-salsa20.exe $(PERF_LIBS)

test-unit-salsa20: test-salsa20.exe
	./test-salsa20.exe unit-test

test-perf-salsa20: test-salsa20.exe
	./test-salsa20.exe perf

#
# Tests for Chacha20
#

test-chacha20.exe:
	$(CC_BASE) $(HACL_HOME)/$(SNAPSHOT_DIR)/Hacl_Chacha20.c test-files/test-chacha.c -o test-chacha20.exe $(PERF_LIBS)

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
	$(CC_BASE) -lpthread $(LIBDL) $(LIBWINSOCK) \
	$(HACL_HOME)/$(SNAPSHOT_DIR)/Hacl_Chacha20_Vec128.c test-files/test-chacha-vec128.c -o test-chacha20-vec128.exe $(PERF_LIBS)
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
	$(CC_BASE) -lpthread $(LIBDL) $(HACL_HOME)/$(SNAPSHOT_DIR)/Hacl_Curve25519.c test-files/test-curve.c -o test-curve25519.exe $(PERF_LIBS)

test-unit-curve25519: test-curve25519.exe
	./test-curve25519.exe unit-test

test-perf-curve25519: test-curve25519.exe
	./test-curve25519.exe perf

#
# Tests for SHA2_512
#

test-sha512.exe:
	$(CC_BASE) -lpthread $(LIBDL) $(HACL_HOME)/$(SNAPSHOT_DIR)/Hacl_SHA2_512.c test-files/test-sha512.c -o test-sha512.exe $(PERF_LIBS)

test-unit-sha512: test-sha512.exe
	./test-sha512.exe unit-test

test-perf-sha512: test-sha512.exe
	./test-sha512.exe perf

#
# Tests for Ed25519
#

test-ed25519.exe:
	$(CC_BASE) -lpthread $(LIBDL) $(HACL_HOME)/$(SNAPSHOT_DIR)/Hacl_SHA2_512.c $(HACL_HOME)/$(SNAPSHOT_DIR)/Hacl_Ed25519.c test-files/test-ed25519.c -o test-ed25519.exe $(PERF_LIBS)

test-unit-ed25519: test-ed25519.exe
	./test-ed25519.exe unit-test

test-perf-ed25519: test-ed25519.exe
	./test-ed25519.exe perf

#
# Tests for the SecretBox API
#

test-secretbox.exe:
	$(CC) $(CFLAGS) -c $(HACL_HOME)/$(SNAPSHOT_DIR)/Hacl_Salsa20.c     -o Hacl_Salsa20.o
	$(CC) $(CFLAGS) -c $(HACL_HOME)/$(SNAPSHOT_DIR)/Hacl_Poly1305_64.c -o Hacl_Poly1305_64.o
	$(CC) $(CFLAGS) -c $(HACL_HOME)/$(SNAPSHOT_DIR)/Hacl_Curve25519.c  -o Hacl_Curve25519.o
	$(CC_BASE) Hacl_Salsa20.o Hacl_Poly1305_64.o Hacl_Curve25519.o \
		$(HACL_HOME)/$(SNAPSHOT_DIR)/Hacl_Policies.c $(HACL_HOME)/$(SNAPSHOT_DIR)/NaCl.c test-files/test-secretbox.c -o test-secretbox.exe $(PERF_LIBS)

test-unit-secretbox: test-secretbox.exe
	./test-secretbox.exe unit-test

test-perf-secretbox: test-secretbox.exe
	./test-secretbox.exe perf

#
# Test for the Box API
#

test-box.exe:
	$(CC) $(CFLAGS) -c $(HACL_HOME)/$(SNAPSHOT_DIR)/Hacl_Salsa20.c     -o Hacl_Salsa20.o
	$(CC) $(CFLAGS) -c $(HACL_HOME)/$(SNAPSHOT_DIR)/Hacl_Poly1305_64.c -o Hacl_Poly1305_64.o
	$(CC) $(CFLAGS) -c $(HACL_HOME)/$(SNAPSHOT_DIR)/Hacl_Curve25519.c  -o Hacl_Curve25519.o
	$(CC_BASE) Hacl_Salsa20.o Hacl_Poly1305_64.o Hacl_Curve25519.o \
		$(HACL_HOME)/$(SNAPSHOT_DIR)/Hacl_Policies.c $(HACL_HOME)/$(SNAPSHOT_DIR)/NaCl.c test-files/test-box.c -o test-box.exe $(PERF_LIBS)

test-unit-box: test-box.exe
	./test-box.exe unit-test

test-perf-box: test-box.exe
	./test-box.exe perf

#
# Tests for the AEAD API
#

test-aead.exe:
	$(CC) $(CFLAGS) -c $(HACL_HOME)/$(SNAPSHOT_DIR)/Hacl_Chacha20.c         -o Hacl_Chacha20.o
	$(CC) $(CFLAGS) -c $(HACL_HOME)/$(SNAPSHOT_DIR)/AEAD_Poly1305_64.c -o AEAD_Poly1305_64.o
	$(CC_BASE) -lpthread $(LIBDL) $(LIBWINSOCK) Hacl_Chacha20.o AEAD_Poly1305_64.o \
		$(HACL_HOME)/$(SNAPSHOT_DIR)/Hacl_Policies.c $(HACL_HOME)/$(SNAPSHOT_DIR)/Chacha20Poly1305.c test-files/test-aead.c -o test-aead.exe $(PERF_LIBS)

test-unit-aead: test-aead.exe
	./test-aead.exe unit-test

test-perf-aead: test-aead.exe
	./test-aead.exe perf

#
# Tests for Vale
#

test-vale:
	$(MAKE) -C ../secure_api krml-test-vale.exe
	$(MAKE) -C ../secure_api krml-test-hacl.exe

test-vale-asm:
	$(MAKE) -C ../secure_api/vale/asm/

#
# Tests for LowCProvider
#

test-provider-lowc:
	$(MAKE) -C ../secure_api/LowCProvider

#
# Tests for applications
#

test-pneutube:
	$(MAKE) -C ../apps/pneutube tube-star.exe

#
# Additionnal targets
#

clean:
	rm -rf *~ *.o *.exe

