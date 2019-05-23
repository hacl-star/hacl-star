CC=/usr/bin/gcc
CFLAGS= -O3 -fomit-frame-pointer -march=native -fPIC
LDFLAGS=-lcrypto

SOURCES= cbd.c consts.c indcpa.c kem.c poly.c polyvec.c PQCgenKAT_kem.c rng.c verify.c \
			   aes256ctr.c invntt.s ntt.s rejsample.c fq.s shuffle.s basemul.S
HEADERS= api.h cbd.h indcpa.h ntt.h params.h poly.h polyvec.h reduce.h rng.h verify.h rejsample.h fq.h shuffle.h symmetric.h \
				 aes256ctr.h

PQCgenKAT_kem: $(HEADERS) $(SOURCES)
	$(CC) $(CFLAGS) -DKYBER_90S -o $@ $(SOURCES) $(LDFLAGS)

.PHONY: clean

clean:
	-rm PQCgenKAT_kem



