FSTAR_HOME   ?= /opt/fstar
KREMLIN_HOME ?= /opt/kremlin

CC=gcc-6 -flto

.PHONY: test clean

test: test-aead test-random test-sha2

test-aead:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	-I $(KREMLIN_HOME)/kremlib $(KREMLIN_HOME)/kremlib/kremlib.c $(KREMLIN_HOME)/kremlib/testlib.c Chacha20.c Poly1305_64.c aead_chacha20_poly1305.c test-aead.c -o test-aead.exe
	./test-aead.exe

test-random:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	-I $(KREMLIN_HOME)/kremlib $(KREMLIN_HOME)/kremlib/kremlib.c $(KREMLIN_HOME)/kremlib/testlib.c cpuid.c drng.c Random.c test-random.c -o test-random.exe
	./test-random.exe

test-sha2:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	-I $(KREMLIN_HOME)/kremlib $(KREMLIN_HOME)/kremlib/kremlib.c $(KREMLIN_HOME)/kremlib/testlib.c SHA2_256.c test-sha2.c -o test-sha2.exe
	./test-sha2.exe

test-hmac-sha2:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	-I $(KREMLIN_HOME)/kremlib $(KREMLIN_HOME)/kremlib/kremlib.c $(KREMLIN_HOME)/kremlib/testlib.c HMAC_SHA2_256.c test-hmac-sha2.c -o test-hmac-sha2.exe
	./test-hmac-sha2.exe

clean:
	rm -rf *~ *.exe *.out 
