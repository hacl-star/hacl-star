.PHONY: test clean

test: test-poly	test-chacha test-salsa test-curve

#CC=/usr/local/opt/llvm/bin/clang
CC=gcc-6

test-poly:
	$(CC) -flto -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	openssl/libcrypto.a kremlib.c testlib.c Poly1305_64.c test-poly.c -l sodium -I openssl  -o test-poly.exe 
	./test-poly.exe

poly.asm:
	$(CC) -flto -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	Poly1305_64.c -S -fverbose-asm -o poly.asm


test-salsa:
	$(CC) -flto -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	kremlib.c testlib.c Salsa20.c test-salsa.c -l sodium -o test-salsa.exe
	./test-salsa.exe

salsa.asm:
	$(CC) -flto -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	Salsa20.c -S -fverbose-asm -o salsa.asm

test-chacha:
	$(CC) -flto -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	openssl/libcrypto.a kremlib.c testlib.c Chacha20.c test-chacha.c -l sodium -o test-chacha.exe -I openssl
	./test-chacha.exe

test-chacha-avx:
	$(CC) -flto -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	stream.c test-goll.c -o test-chacha-avx.exe
	./test-chacha-avx.exe

chacha.asm:
	$(CC) -flto -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	Chacha20.c -S -fverbose-asm -o chacha.asm


test-curve:
	$(CC) -flto -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	openssl/libcrypto.a openssl/libssl.a kremlib.c testlib.c Curve25519.c test-curve.c -l sodium -o test-curve.exe -I openssl/include -I openssl/crypto/ec -I openssl
	./test-curve.exe

test-curve-32:
	$(CC) -flto -Ofast -march=native -mtune=native -m32 -fwrapv -fomit-frame-pointer -funroll-loops -fmath-errno \
	openssl/libcrypto.a openssl/libssl.a kremlib.c testlib.c Curve25519.c test-curve.c -l sodium -o test-curve.exe -I openssl/include -I openssl/crypto/ec -I openssl
	./test-curve.exe

test-nacl:
	$(CC) -flto -Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
	kremlib.c testlib.c Hacl_Policies.c HSalsa20.c Salsa20.c Poly1305_64.c Curve25519.c NaCl.c test-nacl.c -l sodium -o test-nacl.exe
	./test-nacl.exe

clean:
	rm -rf *~ *.exe *.out 
