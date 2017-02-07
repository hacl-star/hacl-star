.PHONY: test clean

OPENSSL_HOME=../../other_providers/openssl
LIBSODIUM_HOME=../../other_providers/libsodium/src/libsodium
CC=gcc-6 -flto

test: test-poly	test-chacha test-salsa test-curve test-nacl


test-poly:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	-I $(OPENSSL_HOME)/crypto/include -I $(OPENSSL_HOME)/crypto/poly1305 $(OPENSSL_HOME)/libcrypto.a \
	-l sodium \
	kremlib.c testlib.c Poly1305_64.c test-poly.c -o test-poly.exe 
	./test-poly.exe

poly.asm:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	Poly1305_64.c -S -fverbose-asm -o poly.asm


test-salsa:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	kremlib.c testlib.c Salsa20.c test-salsa.c -l sodium -o test-salsa.exe
	./test-salsa.exe

test-salsa-avx:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops -mavx -mavx2 \
	kremlib.c testlib.c Salsa20_avx.c test-salsa.c -l sodium -o test-salsa-avx.exe 
	./test-salsa-avx.exe


salsa.asm: Salsa20.c
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	Salsa20.c -l sodium -S -fverbose-asm -o salsa.asm


salsa_avx.asm: Salsa20_avx.c
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	Salsa20_avx.c -l sodium -S -fverbose-asm -o salsa_avx.asm

test-chacha:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	-I $(OPENSSL_HOME)/crypto/include -I $(OPENSSL_HOME)/crypto/poly1305 $(OPENSSL_HOME)/libcrypto.a \
	-l sodium \
	kremlib.c testlib.c Chacha20.c test-chacha.c -o test-chacha.exe
	./test-chacha.exe

chacha.asm:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	Chacha20.c -S -fverbose-asm -o chacha.asm


test-chacha-avx:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	stream.c test-goll.c -o test-chacha-avx.exe
	./test-chacha-avx.exe


test-curve:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	-I $(OPENSSL_HOME) -I $(OPENSSL_HOME)/include -I $(OPENSSL_HOME)/crypto/ec $(OPENSSL_HOME)/libcrypto.a $(OPENSSL_HOME)/libssl.a \
	-l sodium \
	kremlib.c testlib.c Curve25519.c test-curve.c -o test-curve.exe 
	./test-curve.exe

test-nacl:
	$(CC) -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops -flto \
	kremlib.c testlib.c Hacl_Policies.c HSalsa20.c Salsa20.c Poly1305_64.c Curve25519.c NaCl.c test-nacl.c -l sodium -o test-nacl.exe
	./test-nacl.exe

clean:
	rm -rf *~ *.exe *.out 
