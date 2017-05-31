GFIND=$(shell which gfind >/dev/null 2>&1 && echo gfind || echo find)
GCC=$(shell which gcc-7 >/dev/null 2>&1 && echo gcc-7 || (which gcc-6 >/dev/null 2>&1 && echo gcc-6 || echo gcc))
GCC_OPTS=-flto -std=c11 -D_GNU_SOURCE

SNAPSHOT_DIR=snapshot

snapshot/libhacl.so:
	$(MAKE) -C hacl-c CC="$(GCC) $(GCC_OPTS) -fPIC" lib

libhacl: snapshot/libhacl.so

test-snapshot: snapshot
	$(MAKE) -C snapshot CC="$(GCC) $(GCC_OPTS)" test

test:
	$(MAKE) -C hacl-c CC="$(CC) -fno-tree-vectorize -flto" CCOPTS="-Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops " test

test-gcc:
	$(MAKE) -C snapshot-gcc CC="$(GCC) -fno-tree-vectorize -flto" CCOPTS="-Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops " test

test-ccomp:
	$(MAKE) -C snapshot-ccomp CC=ccomp CCOPTS="-O3 -DKRML_NOUINT128 -DKRML_NOSTRUCT_PASSING -finline-asm -D_BSD_SOURCE -D_DEFAULT_SOURCE" test

test-gcc-unrolled:
	$(MAKE) -C snapshot-gcc-unrolled CC="$(GCC) -fno-tree-vectorize -flto" CCOPTS="-Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops " test

echo-perf:
	$(shell (echo -e "Benchmarking results with $(CC) -fno-tree-vectorize -flto -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops\n\nAlgorithm       HACL(cy/b)      LibSodium(cy/b) OpenSSL(cy/b)   TweetNaCl(cy/b) HACL(us/b)      LibSodium(us/b) OpenSSL(us/b)   TweetNaCl(us/b) \n"; cat hacl-c/bench.txt) > benchmark-cc.txt)

perf:
	$(MAKE) -B -C hacl-c CC="$(CC) -fno-tree-vectorize -flto" CCOPTS="-Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops " perf
	$(MAKE) -B echo-perf

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

clean:
	rm -f *.exe *.o *~
	$(MAKE) -C hacl-c clean
	$(MAKE) -C snapshot-gcc clean
	$(MAKE) -C snapshot-gcc-unrolled clean
	$(MAKE) -C snapshot-ccomp clean
