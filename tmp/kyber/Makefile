CC 		    = /usr/bin/cc
CFLAGS    = -g -Wall -Wextra -O3 -fomit-frame-pointer -march=native -fPIC
NISTFLAGS = -O3 -fomit-frame-pointer -march=native -fPIC
RM 		    = /bin/rm

all: testvectors768

SOURCES = poly.c polyvec.c fips202.c reduce.c cbd.c precomp.c ntt.c indcpa.c
HEADERS = params.h poly.h polyvec.h reduce.h cbd.h ntt.h indcpa.h

testvectors768: $(SOURCES) $(HEADERS) testvectors.c
	$(CC) $(CFLAGS) -DKYBER_K=3 $(SOURCES) testvectors.c -o $@


.PHONY: clean test

clean:
	-$(RM) *.o
	-$(RM) -r testvectors768
