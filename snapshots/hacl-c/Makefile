.PHONY: test clean

TWEETNACL_HOME   ?=../../other_providers/tweetnacl
OPENSSL_HOME   ?=../../other_providers/openssl
LIBSODIUM_HOME ?=../../other_providers/libsodium/src/libsodium
CC=gcc-6 -fno-tree-vectorize #-flto

test: test-poly	test-chacha test-salsa test-curve test-secretbox test-box test-aead

test-poly:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	-I $(OPENSSL_HOME)/crypto/include -I $(OPENSSL_HOME)/crypto/poly1305 \
	-I $(TWEETNACL_HOME) $(TWEETNACL_HOME)/tweetnacl.c \
	kremlib.c testlib.c Poly1305_64.c test-poly.c -o test-poly.exe \
	-lsodium $(OPENSSL_HOME)/libcrypto.a
	./test-poly.exe

test-salsa:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	Salsa20.c -c -o Salsa20.o
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	-I $(TWEETNACL_HOME) $(TWEETNACL_HOME)/tweetnacl.c \
	kremlib.c testlib.c Salsa20.o test-salsa.c -l sodium -o test-salsa.exe 
	./test-salsa.exe

test-chacha:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	-I $(OPENSSL_HOME)/include -I $(OPENSSL_HOME)/crypto/poly1305 -I ../../other_providers/tweetnacl \
	../../other_providers/tweetnacl/tweetnacl.c kremlib.c testlib.c Chacha20.c test-chacha.c -o test-chacha.exe \
	 $(OPENSSL_HOME)/libcrypto.a -l sodium -lpthread -ldl
	./test-chacha.exe

test-curve:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	-I $(OPENSSL_HOME) -I $(OPENSSL_HOME)/include -I $(OPENSSL_HOME)/crypto/ec \
	-I $(TWEETNACL_HOME) $(TWEETNACL_HOME)/tweetnacl.c \
	kremlib.c testlib.c Curve25519.c test-curve.c -o test-curve.exe \
	$(OPENSSL_HOME)/libcrypto.a $(OPENSSL_HOME)/libssl.a -l sodium
	./test-curve.exe

test-secretbox:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	HSalsa20.c -c -o HSalsa20.o
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	Salsa20.c -c -o Salsa20.o
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	Poly1305_64.c -c -o Poly1305_64.o
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	Curve25519.c -c -o Curve25519.o
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	-I $(TWEETNACL_HOME) $(TWEETNACL_HOME)/tweetnacl.c \
	HSalsa20.o Salsa20.o Poly1305_64.o Curve25519.o kremlib.c testlib.c Hacl_Policies.c NaCl.c test-secretbox.c -l sodium -o test-secretbox.exe
	./test-secretbox.exe

test-aead:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	Chacha20.c -c -o Chacha20.o
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	Poly1305_64.c -c -o Poly1305_64.o
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	Chacha20.o Poly1305_64.o kremlib.c testlib.c Hacl_Policies.c Chacha20Poly1305.c test-aead.c -o test-aead.exe \
	-l sodium  $(OPENSSL_HOME)/libcrypto.a $(OPENSSL_HOME)/libssl.a 
	./test-aead.exe

test-box:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	HSalsa20.c -c -o HSalsa20.o
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	Salsa20.c -c -o Salsa20.o
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	Poly1305_64.c -c -o Poly1305_64.o
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	Curve25519.c -c -o Curve25519.o
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	-I $(TWEETNACL_HOME) $(TWEETNACL_HOME)/tweetnacl.c \
	HSalsa20.o Salsa20.o Poly1305_64.o Curve25519.o kremlib.c testlib.c Hacl_Policies.c NaCl.c test-box.c -l sodium -o test-box.exe
	./test-box.exe

lib:
	$(CC) -fpic -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	HSalsa20.c -c -o HSalsa20.o
	$(CC) -fpic -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	Salsa20.c -c -o Salsa20.o
	$(CC) -fpic -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	Poly1305_64.c -c -o Poly1305_64.o
	$(CC) -fpic -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	Curve25519.c -c -o Curve25519.o
	$(CC) -shared -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	HSalsa20.o Salsa20.o Poly1305_64.o Curve25519.o kremlib.c Hacl_Policies.c NaCl.c \
	-o libhacl.so


clean:
	rm -rf *~ *.exe *.out *.o
