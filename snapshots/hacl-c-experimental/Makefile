FSTAR_HOME   ?= /opt/fstar
KREMLIN_HOME ?= /opt/kremlin

CC=gcc-6 -flto

.PHONY: test clean

test: test-aead

test-aead:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	-I $(KREMLIN_HOME)/kremlib $(KREMLIN_HOME)/kremlib/kremlib.c $(KREMLIN_HOME)/kremlib/testlib.c Chacha20.c Poly1305_64.c aead_chacha20_poly1305.c test-aead.c -o test-aead.exe
	./test-aead.exe

clean:
	rm -rf *~ *.exe *.out 
