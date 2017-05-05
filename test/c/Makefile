.PHONY: test clean

TWEETNACL_HOME?=../../other_providers/tweetnacl
OPENSSL_HOME?=../../other_providers/openssl
LIBSODIUM_HOME ?=../../other_providers/libsodium/src/libsodium
CC=gcc-6 -fno-tree-vectorize -flto
CCOPTS= -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops 

test: unit-test-poly unit-test-chacha unit-test-salsa unit-test-curve unit-test-ed25519 unit-test-secretbox unit-test-box unit-test-aead

perf: perf-test-poly perf-test-chacha perf-test-salsa perf-test-curve perf-test-ed25519 perf-test-secretbox perf-test-box perf-test-aead

test-poly.exe:
	$(CC) $(CCOPTS) \
	-I $(OPENSSL_HOME)/crypto/include -I $(OPENSSL_HOME)/crypto/poly1305 \
	-I $(TWEETNACL_HOME) $(TWEETNACL_HOME)/tweetnacl.c \
	kremlib.c testlib.c Poly1305_64.c test-poly.c -o test-poly.exe \
	-lsodium $(OPENSSL_HOME)/libcrypto.a

perf-test-poly: test-poly.exe
	./test-poly.exe perf

unit-test-poly: test-poly.exe
	./test-poly.exe unit-test

test-salsa.exe:
	$(CC) $(CCOPTS) \
	Salsa20.c -c -o Salsa20.o
	$(CC) $(CCOPTS) \
	-I $(TWEETNACL_HOME) $(TWEETNACL_HOME)/tweetnacl.c \
	kremlib.c testlib.c Salsa20.o test-salsa.c -l sodium -o test-salsa.exe 

perf-test-salsa: test-salsa.exe
	./test-salsa.exe perf

unit-test-salsa: test-salsa.exe
	./test-salsa.exe unit-test

test-chacha.exe:
	$(CC) $(CCOPTS) \
	-I $(OPENSSL_HOME)/include -I $(OPENSSL_HOME)/crypto/poly1305 -I ../../other_providers/tweetnacl \
	../../other_providers/tweetnacl/tweetnacl.c kremlib.c testlib.c Chacha20.c test-chacha.c -o test-chacha.exe \
	 $(OPENSSL_HOME)/libcrypto.a -l sodium -lpthread -ldl

perf-test-chacha: test-chacha.exe
	./test-chacha.exe perf

unit-test-chacha: test-chacha.exe
	./test-chacha.exe unit-test

test-curve.exe:
	$(CC) $(CCOPTS) \
	-I $(OPENSSL_HOME) -I $(OPENSSL_HOME)/include -I $(OPENSSL_HOME)/crypto/ec \
	-I $(TWEETNACL_HOME) $(TWEETNACL_HOME)/tweetnacl.c \
	kremlib.c testlib.c Curve25519.c test-curve.c -o test-curve.exe \
	$(OPENSSL_HOME)/libcrypto.a $(OPENSSL_HOME)/libssl.a -l sodium -lpthread -ldl

perf-test-curve: test-curve.exe
	./test-curve.exe perf

unit-test-curve: test-curve.exe
	./test-curve.exe unit-test

test-ed25519.exe: Ed25519.c test-ed25519.c
	$(CC) $(CCOPTS) \
	-I $(OPENSSL_HOME) -I $(OPENSSL_HOME)/include -I $(OPENSSL_HOME)/crypto/ec \
	-I $(TWEETNACL_HOME) $(TWEETNACL_HOME)/tweetnacl.c SHA2_512.c \
	kremlib.c testlib.c $^ -o test-ed25519.exe \
	$(OPENSSL_HOME)/libcrypto.a $(OPENSSL_HOME)/libssl.a -l sodium -lpthread -ldl

perf-test-ed25519: test-ed25519.exe
	./test-ed25519.exe perf

unit-test-ed25519: test-ed25519.exe
	./test-ed25519.exe unit-test

test-secretbox.exe:
	$(CC) $(CCOPTS) \
	Salsa20.c -c -o Salsa20.o
	$(CC) $(CCOPTS) \
	Poly1305_64.c -c -o Poly1305_64.o
	$(CC) $(CCOPTS) \
	Curve25519.c -c -o Curve25519.o
	$(CC) $(CCOPTS) \
	-I $(TWEETNACL_HOME) $(TWEETNACL_HOME)/tweetnacl.c \
	Salsa20.o Poly1305_64.o Curve25519.o kremlib.c testlib.c Hacl_Policies.c NaCl.c test-secretbox.c -l sodium -o test-secretbox.exe

perf-test-secretbox: test-secretbox.exe
	./test-secretbox.exe perf

unit-test-secretbox: test-secretbox.exe
	./test-secretbox.exe unit-test

test-aead.exe:
	$(CC) $(CCOPTS) \
	Chacha20.c -c -o Chacha20.o
	$(CC) $(CCOPTS) \
	AEAD_Poly1305_64.c -c -o AEAD_Poly1305_64.o
	$(CC) $(CCOPTS) \
	Chacha20.o AEAD_Poly1305_64.o kremlib.c testlib.c Hacl_Policies.c Chacha20Poly1305.c test-aead.c -o test-aead.exe \
	-l sodium  $(OPENSSL_HOME)/libcrypto.a $(OPENSSL_HOME)/libssl.a -lpthread -ldl

perf-test-aead: test-aead.exe
	./test-aead.exe	perf

unit-test-aead: test-aead.exe
	./test-aead.exe	unit-test

test-box.exe:
	$(CC) $(CCOPTS) \
	Salsa20.c -c -o Salsa20.o
	$(CC) $(CCOPTS) \
	Poly1305_64.c -c -o Poly1305_64.o
	$(CC) $(CCOPTS) \
	Curve25519.c -c -o Curve25519.o
	$(CC) $(CCOPTS) \
	-I $(TWEETNACL_HOME) $(TWEETNACL_HOME)/tweetnacl.c \
	Salsa20.o Poly1305_64.o Curve25519.o kremlib.c testlib.c Hacl_Policies.c NaCl.c test-box.c -l sodium -o test-box.exe

perf-test-box: test-box.exe
	./test-box.exe perf

unit-test-box: test-box.exe
	./test-box.exe unit-test

lib:
	$(CC) $(CCOPTS) \
	Salsa20.c -c -o Salsa20.o
	$(CC) $(CCOPTS) \
	Poly1305_64.c -c -o Poly1305_64.o
	$(CC) $(CCOPTS) \
	Curve25519.c -c -o Curve25519.o
	$(CC) $(CCOPTS) \
	Chacha20Poly1305.c -c -o Chacha20Poly1305.o
	$(CC) -shared  $(CCOPTS) \
	Salsa20.o Poly1305_64.o Chacha20.o Chacha20Poly1305.o Curve25519.o kremlib.c Hacl_Policies.c NaCl.c \
	-o libhacl.so

lib-test: lib
	$(CC)  $(CCOPTS) \
	-I $(OPENSSL_HOME)/crypto/include -I $(OPENSSL_HOME)/crypto/poly1305 \
	-I $(TWEETNACL_HOME) $(TWEETNACL_HOME)/tweetnacl.c \
	testlib.c test-poly.c -o test-poly.exe \
	-lsodium $(OPENSSL_HOME)/libcrypto.a libhacl.so
	$(CC)  $(CCOPTS) \
	-I $(TWEETNACL_HOME) $(TWEETNACL_HOME)/tweetnacl.c \
	testlib.c test-salsa.c -o test-salsa.exe \
	-lsodium $(OPENSSL_HOME)/libcrypto.a libhacl.so
	$(CC)  $(CCOPTS) \
	-I $(OPENSSL_HOME)/include -I $(OPENSSL_HOME)/crypto/poly1305 -I ../../other_providers/tweetnacl \
	../../other_providers/tweetnacl/tweetnacl.c testlib.c test-chacha.c -o test-chacha.exe \
	 $(OPENSSL_HOME)/libcrypto.a -l sodium -lpthread -ldl libhacl.so
	$(CC)  $(CCOPTS) \
	-I $(TWEETNACL_HOME) $(TWEETNACL_HOME)/tweetnacl.c \
	testlib.c test-secretbox.c -o test-secretbox.exe \
	-lsodium $(OPENSSL_HOME)/libcrypto.a libhacl.so
	$(CC)  $(CCOPTS) \
	testlib.c test-aead.c -o test-aead.exe \
	-l sodium  $(OPENSSL_HOME)/libcrypto.a $(OPENSSL_HOME)/libssl.a -lpthread -ldl libhacl.so
	$(CC)  $(CCOPTS) \
	-I $(OPENSSL_HOME) -I $(OPENSSL_HOME)/include -I $(OPENSSL_HOME)/crypto/ec \
	-I $(TWEETNACL_HOME) $(TWEETNACL_HOME)/tweetnacl.c \
	testlib.c test-curve.c -o test-curve.exe \
	$(OPENSSL_HOME)/libcrypto.a $(OPENSSL_HOME)/libssl.a -l sodium -lpthread -ldl libhacl.so
	$(CC)  $(CCOPTS) \
	-I $(TWEETNACL_HOME) $(TWEETNACL_HOME)/tweetnacl.c \
	testlib.c test-box.c -o test-box.exe -l sodium  libhacl.so
	./test-chacha.exe
	./test-salsa.exe
	./test-poly.exe
	./test-secretbox.exe	
	./test-aead.exe	
	./test-curve.exe
	./test-box.exe



clean:
	rm -rf *~ *.exe *.out *.o
