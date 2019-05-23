CC=/usr/bin/gcc
LDFLAGS=-lcrypto

SOURCES= cbd.c indcpa.c kem.c ntt.c poly.c polyvec.c PQCgenKAT_kem.c reduce.c rng.c verify.c sha256.c sha512.c aes256ctr.c
HEADERS= api.h cbd.h indcpa.h ntt.h params.h poly.h polyvec.h reduce.h rng.h verify.h symmetric.h sha2.h aes256ctr.h

PQCgenKAT_kem: $(HEADERS) $(SOURCES)
	$(CC) -DKYBER_90S -o $@ $(SOURCES) $(LDFLAGS)

.PHONY: clean

clean:
	-rm PQCgenKAT_kem

