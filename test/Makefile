include Makefile.include
include Makefile.build

#
# Unit tests
#

all: extract-all-c
	$(MAKE) -C ../code test
	$(MAKE) test-vale
	$(MAKE) test-vale-asm
	$(MAKE) test-pneutube
	$(MAKE) test-snapshot
	$(MAKE) test-ccomp
	$(MAKE) test-gcc
	$(MAKE) test-gcc-unrolled
	$(MAKE) -C openssl-engine

test-vale:
	$(MAKE) -C ../secure_api krml-test-vale.exe
	$(MAKE) -C ../secure_api krml-test-hacl.exe

test-pneutube:
	$(MAKE) -C ../apps/pneutube tube-star.exe

test-vale-asm:
	$(MAKE) -C ../secure_api/vale/asm/

test-snapshot: snapshot
	$(MAKE) -C snapshot CC="$(GCC) $(GCC_OPTS)" test

test-ccomp:
	$(MAKE) -C snapshot-ccomp CC=ccomp CCOPTS="-O3 -DKRML_NOUINT128 -DKRML_NOSTRUCT_PASSING -finline-asm -D_BSD_SOURCE -D_DEFAULT_SOURCE" test

test-gcc:
	$(MAKE) -C snapshot-gcc CC="$(GCC) -fno-tree-vectorize $(ENABLE_LTO)" CCOPTS="-Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops " test

test-gcc-unrolled:
	$(MAKE) -C snapshot-gcc-unrolled CC="$(GCC) -fno-tree-vectorize $(ENABLE_LTO)" CCOPTS="-Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops " test


#
# Performance tests
#

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
