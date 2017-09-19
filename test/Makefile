include ../code/Makefile.include

.PHONY: snapshot snapshot-gcc snapshot-ccomp snapshot-msvc snapshot-gcc-unrolled

HAS_CL=$(shell which cl.exe >/dev/null 2>&1 && echo true || echo false)
HAS_CCOMP=$(shell which ccomp >/dev/null 2>&1 && echo true || echo false)

GFIND=$(shell which gfind >/dev/null 2>&1 && echo gfind || echo find)

SNAPSHOT_DIR=snapshot

all: extract-specs extract-all-c ct verify-all
	$(MAKE) -C ../code test
	# JK: moved to parallel build (otherwise spec tests are too slow)
	#$(MAKE) -C .. verify
	$(MAKE) compile-vale
	$(MAKE) -C openssl-engine
	$(MAKE) -B update-snapshot
	# JK: TODO MSVC & CompCert compilation tests

travis: extract-c-code ct
	$(MAKE) -C .. world

extract-specs:
	$(MAKE) -C $(HACL_HOME)/specs

extract-c-code:
	$(GFIND) ../code -name out.krml -exec touch {} \;
	$(MAKE) -C $(HACL_HOME)/code extract-c

extract-c-code-experimental:
	$(MAKE) -C $(HACL_HOME)/code/experimental/ extract-c

extract-c-crypto:
	$(MAKE) -C ../secure_api krml-test-vale.exe
	$(MAKE) -C ../secure_api krml-test-hacl.exe

extract-c-apps:
	$(MAKE) -C ../apps/pneutube tube-star.exe

# JK: fixme, extract-c-apps to be added to the regression tests when
# LibSodium is added to the build machine
extract-c: extract-c-code extract-c-crypto # extract-c-apps

# These cannot benefit from parallelism, tests C extraction for available compilers
extract-all-c:
	if $(HAS_CCOMP); then $(MAKE) clean ; USE_CCOMP=true $(MAKE) extract-c ; fi
	if $(HAS_CL); then $(MAKE) clean ; USE_CL=true $(MAKE) extract-c ; fi
	$(MAKE) clean ; $(MAKE) extract-c

compile-vale:
	$(MAKE) -C ../secure_api/vale/asm/

ct:
	$(MAKE) -C ../code ct

verify-specs:
	$(MAKE) -C ../specs all-ver

verify-code:
	$(MAKE) -C ../code ci

verify-crypto:
	$(MAKE) -C ../secure_api all-ver

verify-all:
	$(MAKE) -C .. verify

hints:
	$(info The 'test' directory does not contain .fst files, so no hints to generate.)

verify: 
	$(info The 'test' directory does not contain .fst files, so no verification to run.)

SNAPSHOT_FILES= ./c/* \
	$(addprefix ../code/poly1305/poly-c/, Poly1305_64.* AEAD_Poly1305_64.*) \
	../code/curve25519/x25519-c/Curve25519.* \
	../code/salsa-family/chacha-c/Chacha20.* \
	../code/salsa-family/salsa-c/Salsa20.* \
	$(addprefix ../code/api/aead-c/, Chacha20Poly1305.*) \
	$(addprefix ../code/api/box-c/, NaCl.*) \
	$(addprefix ../code/api/policies-c/, Hacl_Policies.* ) \
	$(addprefix ../code/ed25519/ed25519-c/, Ed25519.*) \
	$(addprefix ../code/hash/sha2-c/, SHA2_256.*) \
	$(addprefix ../code/hash/sha2-c/, SHA2_384.*) \
	$(addprefix ../code/hash/sha2-c/, SHA2_512.*) \
	$(addprefix ../code/hmac/hmac-c/, HMAC_SHA2_256.*) \
	$(addprefix ../code/salsa-family/chacha-vec128-c/, Chacha20_Vec128.* ../vec128.h)

build-snapshot: 
	mkdir -p $(SNAPSHOT_DIR)
	cp $(SNAPSHOT_FILES) $(SNAPSHOT_DIR)/
	touch $(SNAPSHOT_DIR)/Prims.h
	$(MAKE) -C $(SNAPSHOT_DIR) clean

ifeq ($(OS),Windows_NT)
  GCC=x86_64-w64-mingw32-gcc.exe
else
  GCC=$(shell which gcc-7 >/dev/null 2>&1 && echo gcc-7 || (which gcc-6 >/dev/null 2>&1 && echo gcc-6 || echo gcc))
  ENABLE_LTO=-flto
endif
GCC_OPTS=$(ENABLE_LTO) -std=c11 -D_GNU_SOURCE

snapshot/libhacl.so: snapshot
	$(MAKE) -C snapshot CC="$(GCC) $(GCC_OPTS) -fPIC" lib

test-snapshot: snapshot
	$(MAKE) -C snapshot CC="$(GCC) $(GCC_OPTS)" test

test-ccomp:
	$(MAKE) -C snapshot-ccomp CC=ccomp CCOPTS="-O3 -DKRML_NOUINT128 -DKRML_NOSTRUCT_PASSING -finline-asm -D_BSD_SOURCE -D_DEFAULT_SOURCE" test

test-gcc:
	$(MAKE) -C snapshot-gcc CC="$(GCC) -fno-tree-vectorize $(ENABLE_LTO)" CCOPTS="-Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops " test

test-gcc-unrolled:
	$(MAKE) -C snapshot-gcc-unrolled CC="$(GCC) -fno-tree-vectorize $(ENABLE_LTO)" CCOPTS="-Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops " test

echo-perf-ccomp:
	$(shell (echo -e "Benchmarking results with ccomp -O3 -DKRML_NOUINT128 -DKRML_NOSTRUCT_PASSING -finline-asm -D_BSD_SOURCE -D_DEFAULT_SOURCE\n\nAlgorithm       HACL(cy/b)      LibSodium(cy/b) OpenSSL(cy/b)   TweetNaCl(cy/b) HACL(us/b)      LibSodium(us/b) OpenSSL(us/b)   TweetNaCl(us/b) \n"; cat snapshot-ccomp/bench.txt) > benchmark-compcert.txt)

perf-ccomp:
	-$(MAKE) -B -C snapshot-ccomp CC=ccomp CCOPTS="-O3 -DKRML_NOUINT128 -DKRML_NOSTRUCT_PASSING -finline-asm -D_BSD_SOURCE -D_DEFAULT_SOURCE" perf
	$(MAKE) -B echo-perf-ccomp

echo-perf-gcc:
	$(shell (echo -e "Benchmarking results with $(GCC) -fno-tree-vectorize $(ENABLE_LTO) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops\n\nAlgorithm       HACL(cy/b)      LibSodium(cy/b) OpenSSL(cy/b)   TweetNaCl(cy/b) HACL(us/b)      LibSodium(us/b) OpenSSL(us/b)   TweetNaCl(us/b) \n"; cat snapshot-gcc/bench.txt) > benchmark-gcc.txt)

perf-gcc:
	$(MAKE) -B -C snapshot-gcc CC="$(GCC) -fno-tree-vectorize $(ENABLE_LTO)" CCOPTS="-Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops " perf
	$(MAKE) -B echo-perf-gcc

echo-gcc-unrolled:
	$(shell (echo -e "Benchmarking results with $(GCC) -fno-tree-vectorize $(ENABLE_LTO) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops with KreMLin loop unrolling\n\nAlgorithm       HACL(cy/b)      LibSodium(cy/b) OpenSSL(cy/b)   TweetNaCl(cy/b) HACL(us/b)      LibSodium(us/b) OpenSSL(us/b)   TweetNaCl(us/b) \n"; cat snapshot-gcc-unrolled/bench.txt) > benchmark-gcc-unrolled.txt)

perf-gcc-unrolled:
	$(MAKE) -B -C snapshot-gcc-unrolled CC="$(GCC) -fno-tree-vectorize $(ENABLE_LTO)" CCOPTS="-Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops " perf
	$(MAKE) -B echo-gcc-unrolled

all-perf:
	$(MAKE) perf-gcc
	$(MAKE) perf-gcc-unrolled
	$(MAKE) perf-ccomp

snapshot:
	$(MAKE) extract-c-code extract-c-code-experimental
	$(MAKE) build-snapshot

snapshot-ccomp:
	if $(HAS_CCOMP); then $(MAKE) -B extract-c-code extract-c-code-experimental KOPTS="-cc compcert -funroll-loops 10 -fnouint128 -fnostruct-passing"; fi
	if $(HAS_CCOMP); then $(MAKE) -B build-snapshot SNAPSHOT_DIR=snapshot-ccomp; fi

snapshot-msvc:
	if $(HAS_CL); then $(MAKE) extract-c-code extract-c-code-experimental KOPTS="-cc msvc -drop FStar"; fi
	if $(HAS_CL); then $(MAKE) build-snapshot SNAPSHOT_DIR=snapshot-msvc; fi

snapshot-gcc:
	$(MAKE) -B extract-c-code extract-c-code-experimental KOPTS="-drop FStar"
	$(MAKE) -B build-snapshot SNAPSHOT_DIR=snapshot-gcc

snapshot-gcc-unrolled:
	$(MAKE) -B extract-c-code extract-c-code-experimental KOPTS="-funroll-loops 5 -drop FStar"
	$(MAKE) -B build-snapshot SNAPSHOT_DIR=snapshot-gcc-unrolled

all-snapshots:
	$(MAKE) snapshot-ccomp
	$(MAKE) -C ../code clean
	$(MAKE) snapshot-msvc
	$(MAKE) -C ../code clean
	$(MAKE) snapshot-gcc
	$(MAKE) -C ../code clean
	$(MAKE) snapshot-gcc-unrolled
	$(MAKE) -C ../code clean

update-snapshot:
	$(MAKE) snapshot-gcc
	$(MAKE) -C ../code clean
	$(MAKE) snapshot-gcc-unrolled
	$(MAKE) -C ../code clean
	$(MAKE) -C snapshot-gcc-unrolled clean
	$(MAKE) -C snapshot-gcc clean
	cp $(addprefix snapshot-gcc/, AEAD_Poly1305_64.* Chacha20.* Chacha20Poly1305.* Chacha20_Vec128.* gcc_compat.h Hacl_Policies.* hacl_test_utils.* NaCl.* Poly1305_64.* Salsa20.* SHA2_* test* vec128.h) \
	   $(addprefix snapshot-gcc-unrolled/, Curve25519* Ed25519*) \
	   $(addprefix c/, kremlib.h kremlib.c FStar.h Makefile)  \
		../snapshots/hacl-c
	$(MAKE) -C ../snapshots/hacl-c unit-tests
	$(MAKE) -C ../snapshots/hacl-c unit-tests-32
	$(MAKE) -C ../snapshots/hacl-c perf
	$(MAKE) -C ../snapshots/hacl-c clean

nss-snapshot:
	$(MAKE) snapshot-gcc
	$(MAKE) -C ../code clean
	$(MAKE) snapshot-gcc-unrolled
	$(MAKE) -C ../code clean
	$(MAKE) -C snapshot-gcc-unrolled clean
	$(MAKE) -C snapshot-gcc clean
	mkdir -p ../snapshots/nss
	cp $(addprefix snapshot-gcc/, AEAD_Poly1305_64.* Chacha20.* Chacha20Poly1305.* Chacha20_Vec128.* gcc_compat.h Hacl_Policies.* hacl_test_utils.* kremlib.* NaCl.* Poly1305_64.* Salsa20.* SHA2_* test* vec128.h) ../snapshots/nss
	cp $(addprefix snapshot-gcc-unrolled/, Curve25519* Ed25519*) ../snapshots/nss
	cp $(addprefix c/, kremlib.h kremlib?c FStar.h Makefile)  ../snapshots/nss
	$(MAKE) -C ../snapshots/nss unit-tests
	$(MAKE) -C ../snapshots/nss unit-tests-32
	$(MAKE) -C ../snapshots/nss clean

clean:
	$(MAKE) -C ../code clean
	$(MAKE) -C ../secure_api clean
	rm -rf snapshot snapshot-ccomp snapshot-msvc snapshot-gcc snapshot-gcc-unrolled *.o *.exe *~
