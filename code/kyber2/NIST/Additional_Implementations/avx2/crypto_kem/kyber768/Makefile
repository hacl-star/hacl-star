CC=/usr/bin/gcc
CFLAGS= -O3 -fomit-frame-pointer -march=native -fPIC
LDFLAGS=-lcrypto

SOURCES= cbd.c consts.c fips202.c fips202x4.c indcpa.c kem.c poly.c polyvec.c PQCgenKAT_kem.c rng.c verify.c \
			   invntt.s ntt.s rejsample.c fq.s shuffle.s basemul.S \
         keccak4x/KeccakP-1600-times4-SIMD256.c symmetric-fips202.c
HEADERS= api.h cbd.h fips202.h fips202x4.h indcpa.h ntt.h params.h poly.h polyvec.h reduce.h rng.h verify.h rejsample.h fq.h shuffle.h symmetric.h \
         keccak4x/align.h keccak4x/brg_endian.h keccak4x/KeccakP-1600-times4-SnP.h keccak4x/KeccakP-1600-unrolling.macros keccak4x/SIMD256-config.h

PQCgenKAT_kem: $(HEADERS) $(SOURCES)
	$(CC) $(CFLAGS) -o $@ $(SOURCES) $(LDFLAGS)

.PHONY: clean

clean:
	-rm PQCgenKAT_kem
