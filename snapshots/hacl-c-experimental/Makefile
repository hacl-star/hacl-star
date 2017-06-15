FSTAR_HOME   ?= ../../dependencies/FStar
KREMLIN_HOME ?= ../../dependencies/kremlin
OPENSSL_HOME ?= ../../dependencies/openssl
LIBSODIUM_HOME ?= ../../dependencies/libsodium


CC=gcc-7 -flto

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

test-sha2_256:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	-I $(OPENSSL_HOME)/include -I $(LIBSODIUM)/local/include -I $(KREMLIN_HOME)/kremlib $(KREMLIN_HOME)/kremlib/kremlib.c $(KREMLIN_HOME)/kremlib/testlib.c SHA2_256.c test-sha2_256.c -o test-sha2_256.exe $(OPENSSL_HOME)/libcrypto.a $(LIBSODIUM_HOME)/local/lib/libsodium.a
	./test-sha2_256.exe

test-sha2_512:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	-I $(OPENSSL_HOME)/include -I $(LIBSODIUM)/local/include -I $(KREMLIN_HOME)/kremlib $(KREMLIN_HOME)/kremlib/kremlib.c $(KREMLIN_HOME)/kremlib/testlib.c SHA2_512.c test-sha2_512.c -o test-sha2_512.exe $(OPENSSL_HOME)/libcrypto.a $(LIBSODIUM_HOME)/local/lib/libsodium.a
	./test-sha2_512.exe

clean:
	rm -rf *~ *.exe *.out 
