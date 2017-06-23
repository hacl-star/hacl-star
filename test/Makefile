HACL_HOME=$(CURDIR)/..
include ../code/Makefile.include

.PHONY: snapshot snapshot-gcc snapshot-ccomp snapshot-msvc snapshot-gcc-unrolled

HAS_CL=$(shell which cl.exe >/dev/null 2>&1 && echo true || echo false)
HAS_CCOMP=$(shell which ccomp >/dev/null 2>&1 && echo true || echo false)

GFIND=$(shell which gfind >/dev/null 2>&1 && echo gfind || echo find)

SNAPSHOT_DIR=snapshot

all:
	$(MAKE) extract-specs extract-all-c ct verify
	$(MAKE) compile-vale
	$(MAKE) -C openssl-engine
	$(MAKE) -B build-snapshot SNAPSHOT_DIR=snapshot-gcc
	# JP: fixme, doesn't work on build machine
	# $(MAKE) -C snapshot-gcc

travis:
	$(MAKE) extract-c-code
	$(MAKE) ct
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
	if $(HAS_CCOMP); then $(MAKE) extract-c KREMLIN_ARGS="-cc compcert"; fi
	if $(HAS_CL); then $(MAKE) extract-c KREMLIN_ARGS="-cc msvc"; fi
	$(MAKE) extract-c

compile-vale:
	$(MAKE) -C ../secure_api/vale/asm/

ct:
	$(MAKE) -C ../code ct

verify-specs:
	$(MAKE) -C ../specs all-ver

verify-code:
	$(MAKE) -C ../code ci

verify-crypto:
	# Note: the all-hints target fails silently.
	$(MAKE) -C ../secure_api all-ver OTHERFLAGS="--record_hints"

hints-code:
	$(MAKE) -C ../code hints

hints-crypto:
	$(MAKE) -C ../secure_api hints

hints: hints-code hints-crypto

verify: verify-code verify-crypto

build-snapshot:
	mkdir -p $(SNAPSHOT_DIR)
	cp $(addprefix ../code/poly1305/poly-c/, Poly1305_64.* AEAD_Poly1305_64.*) \
		../code/curve25519/x25519-c/Curve25519.* \
		../code/salsa-family/chacha-c/Chacha20.* \
		../code/salsa-family/salsa-c/Salsa20.* \
		$(addprefix ../code/api/aead-c/, Chacha20Poly1305.*) \
		$(addprefix ../code/api/box-c/, Hacl_Policies.* NaCl.*) \
		$(addprefix ../code/ed25519/ed25519-c/, Ed25519.*) \
		$(addprefix ../code/hash/sha2-256-c/, SHA2_256.*) \
		$(addprefix ../code/hash/sha2-384-c/, SHA2_384.*) \
		$(addprefix ../code/hash/sha2-512-c/, SHA2_512.*) \
		$(addprefix ../code/hmac/hmac-c/, HMAC_SHA2_256.*) \
		$(addprefix ../code/salsa-family/chacha-vec128/, Chacha20_Vec128.* ../vec128.h) \
		 $(SNAPSHOT_DIR)
	cp ./c/* $(SNAPSHOT_DIR)/
	$(MAKE) -C $(SNAPSHOT_DIR) clean

GCC=$(shell which gcc-7 >/dev/null 2>&1 && echo gcc-7 || (which gcc-6 >/dev/null 2>&1 && echo gcc-6 || echo gcc))
GCC_OPTS=-flto -std=c11 -D_GNU_SOURCE

snapshot/libhacl.so: snapshot
	$(MAKE) -C snapshot CC="$(GCC) $(GCC_OPTS) -fPIC" lib

test-snapshot: snapshot
	$(MAKE) -C snapshot CC="$(GCC) $(GCC_OPTS)" test

test-ccomp:
	$(MAKE) -C snapshot-ccomp CC=ccomp CCOPTS="-O3 -DKRML_NOUINT128 -DKRML_NOSTRUCT_PASSING -finline-asm -D_BSD_SOURCE -D_DEFAULT_SOURCE" test

test-gcc:
	$(MAKE) -C snapshot-gcc CC="$(GCC) -fno-tree-vectorize -flto" CCOPTS="-Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops " test

test-gcc-unrolled:
	$(MAKE) -C snapshot-gcc-unrolled CC="$(GCC) -fno-tree-vectorize -flto" CCOPTS="-Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops " test

echo-perf-ccomp:
	$(shell (echo -e "Benchmarking results with ccomp -O3 -DKRML_NOUINT128 -DKRML_NOSTRUCT_PASSING -finline-asm -D_BSD_SOURCE -D_DEFAULT_SOURCE\n\nAlgorithm       HACL(cy/b)      LibSodium(cy/b) OpenSSL(cy/b)   TweetNaCl(cy/b) HACL(us/b)      LibSodium(us/b) OpenSSL(us/b)   TweetNaCl(us/b) \n"; cat snapshot-ccomp/bench.txt) > benchmark-compcert.txt)

perf-ccomp:
	-$(MAKE) -B -C snapshot-ccomp CC=ccomp CCOPTS="-O3 -DKRML_NOUINT128 -DKRML_NOSTRUCT_PASSING -finline-asm -D_BSD_SOURCE -D_DEFAULT_SOURCE" perf
	$(MAKE) -B echo-perf-ccomp

echo-perf-gcc:
	$(shell (echo -e "Benchmarking results with $(GCC) -fno-tree-vectorize -flto -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops\n\nAlgorithm       HACL(cy/b)      LibSodium(cy/b) OpenSSL(cy/b)   TweetNaCl(cy/b) HACL(us/b)      LibSodium(us/b) OpenSSL(us/b)   TweetNaCl(us/b) \n"; cat snapshot-gcc/bench.txt) > benchmark-gcc.txt)

perf-gcc:
	$(MAKE) -B -C snapshot-gcc CC="$(GCC) -fno-tree-vectorize -flto" CCOPTS="-Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops " perf
	$(MAKE) -B echo-perf-gcc

echo-gcc-unrolled:
	$(shell (echo -e "Benchmarking results with $(GCC) -fno-tree-vectorize -flto -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops with KreMLin loop unrolling\n\nAlgorithm       HACL(cy/b)      LibSodium(cy/b) OpenSSL(cy/b)   TweetNaCl(cy/b) HACL(us/b)      LibSodium(us/b) OpenSSL(us/b)   TweetNaCl(us/b) \n"; cat snapshot-gcc-unrolled/bench.txt) > benchmark-gcc-unrolled.txt)

perf-gcc-unrolled:
	$(MAKE) -B -C snapshot-gcc-unrolled CC="$(GCC) -fno-tree-vectorize -flto" CCOPTS="-Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops " perf
	$(MAKE) -B echo-gcc-unrolled

all-perf:
	$(MAKE) perf-gcc
	$(MAKE) perf-gcc-unrolled
	$(MAKE) perf-ccomp

snapshot:
	$(MAKE) extract-c-code extract-c-code-experimental
	$(MAKE) build-snapshot

snapshot-ccomp:
	if $(HAS_CCOMP); then $(MAKE) -B extract-c-code extract-c-code-experimental KREMLIN_ARGS="-cc compcert -funroll-loops 10 -fnouint128 -fnostruct-passing"; fi
	if $(HAS_CCOMP); then $(MAKE) -B build-snapshot SNAPSHOT_DIR=snapshot-ccomp; fi

snapshot-msvc:
	if $(HAS_CL); then $(MAKE) extract-c-code extract-c-code-experimental KREMLIN_ARGS="-cc msvc"; fi
	if $(HAS_CL); then $(MAKE) build-snapshot SNAPSHOT_DIR=snapshot-msvc; fi

snapshot-gcc:
	$(MAKE) -B extract-c-code extract-c-code-experimental
	$(MAKE) -B build-snapshot SNAPSHOT_DIR=snapshot-gcc

snapshot-gcc-unrolled:
	$(MAKE) -B extract-c-code extract-c-code-experimental KREMLIN_ARGS="-funroll-loops 5"
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
	$(build-snapshot)
	$(MAKE) -C snapshot clean
	cp snapshot/*.c snapshot/*.h ../snapshots/hacl-c

clean:
	$(MAKE) -C ../code clean
	$(MAKE) -C ../secure_api clean
	rm -rf snapshot snapshot-ccomp snapshot-msvc snapshot-gcc snapshot-gcc-unrolled *.o *.exe *~
