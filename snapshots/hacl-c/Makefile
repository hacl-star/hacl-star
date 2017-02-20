.PHONY: test clean

OPENSSL_HOME   ?=../../other_providers/openssl
LIBSODIUM_HOME ?=../../other_providers/libsodium/src/libsodium
CC=gcc-6 -flto

test: test-poly	test-chacha test-salsa test-curve test-nacl


test-poly:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	-I $(OPENSSL_HOME)/crypto/include -I $(OPENSSL_HOME)/crypto/poly1305 \
	kremlib.c testlib.c Poly1305_64.c test-poly.c -o test-poly.exe \
	-lsodium $(OPENSSL_HOME)/libcrypto.a
	./test-poly.exe

test-salsa:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops -flto \
	Salsa20.c -c -o Salsa20.o
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	kremlib.c testlib.c Salsa20.o test-salsa.c -l sodium -o test-salsa.exe
	./test-salsa.exe

test-chacha:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	-I $(OPENSSL_HOME)/include -I $(OPENSSL_HOME)/crypto/poly1305 \
	kremlib.c testlib.c Chacha20.c test-chacha.c -o test-chacha.exe \
	 $(OPENSSL_HOME)/libcrypto.a -l sodium -lpthread -ldl
	./test-chacha.exe

test-curve:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	-I $(OPENSSL_HOME) -I $(OPENSSL_HOME)/include -I $(OPENSSL_HOME)/crypto/ec \
	kremlib.c testlib.c Curve25519.c test-curve.c -o test-curve.exe \
	$(OPENSSL_HOME)/libcrypto.a $(OPENSSL_HOME)/libssl.a -l sodium
	./test-curve.exe

test-nacl:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops -flto \
	HSalsa20.c -c -o HSalsa20.o
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops -flto \
	Salsa20.c -c -o Salsa20.o
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops -flto \
	Poly1305_64.c -c -o Poly1305_64.o
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops -flto \
	Curve25519.c -c -o Curve25519.o
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops -flto \
	HSalsa20.o Salsa20.o Poly1305_64.o Curve25519.o kremlib.c testlib.c Hacl_Policies.c NaCl.c test-nacl.c -l sodium -o test-nacl.exe
	./test-nacl.exe

clean:
	rm -rf *~ *.exe *.out 
