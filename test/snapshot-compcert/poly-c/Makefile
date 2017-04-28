
cc:
	gcc-6 -O3 testlib.c libkremlin.c -shared -o libkremlin.so -fPIC -g3 -gdwarf-3
	/usr/local/Cellar/compcert/3.0.1_1/bin/ccomp -fpacked-structs -fstruct-passing -finline-asm -O3 -D$(INT128) Poly1305_64.c kremlib.c ../../../other_providers/tweetnacl/tweetnacl.c test-poly.c ../../../other_providers/openssl/libcrypto.a -lsodium -lkremlin -L. -I ../../../other_providers/openssl/crypto/include -I ../../../other_providers/openssl/crypto/poly1305 -I ../../../other_providers/tweetnacl -S -g3 -gdwarf-3
	mv Poly1305_64.s Poly1305_64-cc.s
	/usr/local/Cellar/compcert/3.0.1_1/bin/ccomp -v -fstruct-return -fstruct-passing -finline-asm -O3 -D$(INT128) Poly1305_64.c kremlib.c ../../../other_providers/tweetnacl/tweetnacl.c test-poly.c ../../../other_providers/openssl/libcrypto.a -lsodium -lkremlin -L. -I ../../../other_providers/openssl/crypto/include -I ../../../other_providers/openssl/crypto/poly1305 -I ../../../other_providers/tweetnacl -g3 -gdwarf-3
	mv a.out test-poly-cc.exe
	./test-poly-cc.exe

gcc:
	gcc-6 -O3  testlib.c -shared -o libkremlin.so -fPIC
	gcc-6 -O3  -D$(INT128) -c -S Poly1305_64.c -g
	mv Poly1305_64.s Poly1305_64-gcc.s
	gcc-6 -v -O3 -D$(INT128)  Poly1305_64.c kremlib.c ../../../other_providers/tweetnacl/tweetnacl.c test-poly.c ../../../other_providers/openssl/libcrypto.a -lsodium -lkremlin -L. -I ../../../other_providers/openssl/crypto/include -I ../../../other_providers/openssl/crypto/poly1305 -I ../../../other_providers/tweetnacl -g
	mv a.out test-poly-gcc.exe
	./test-poly-gcc.exe

gcc32:
	gcc-6 -O3 -m32 testlib.c -shared -o libkremlin.so -fPIC
	gcc-6 -O3 -m32 -c -S Poly1305_32.c -g
	mv Poly1305_32.s Poly1305_32-gcc.s
	gcc-6 -v -O3 -m32 -mtune=generic Poly1305_32.c kremlib.c ../../../other_providers/tweetnacl/tweetnacl.c test-poly32.c ../../../other_providers/openssl/libcrypto.a -lsodium -lkremlin -L. -I ../../../other_providers/openssl/crypto/include -I ../../../other_providers/openssl/crypto/poly1305 -I ../../../other_providers/tweetnacl -g
	mv a.out test-poly32-gcc.exe
	./test-poly32-gcc.exe

gcc32-custom:
	gcc-6 -O3 -m32 testlib.c -shared -o libkremlin.so -fPIC
	gcc-6 -O3 -m32 -D$(INT128)-c -S Poly1305_64.c -g
	mv Poly1305_64.s Poly1305_32-gcc.s
	gcc-6 -v -O3 -D$(INT128) -m32 -mtune=generic Poly1305_64.c kremlib.c ../../../other_providers/tweetnacl/tweetnacl.c test-poly.c ../../../other_providers/openssl/libcrypto.a -lsodium -lkremlin -L. -I ../../../other_providers/openssl/crypto/include -I ../../../other_providers/openssl/crypto/poly1305 -I ../../../other_providers/tweetnacl -g
	mv a.out test-poly32-gcc.exe
	./test-poly32-gcc.exe



cc32:
	gcc-6 -O3 -m32 testlib.c -shared -o libkremlin.so -fPIC -g3 -gdwarf-3
	~/Desktop/repositories/CompCert/ccomp -fpacked-structs -fstruct-passing -finline-asm -O3 Poly1305_32.c kremlib.c ../../../other_providers/tweetnacl/tweetnacl.c test-poly32.c ../../../other_providers/openssl/libcrypto.a -lsodium -lkremlin -L. -I ../../../other_providers/openssl/crypto/include -I ../../../other_providers/openssl/crypto/poly1305 -I ../../../other_providers/tweetnacl -S -g3 -gdwarf-3
	mv Poly1305_32.s Poly1305_32-cc.s
	~/Desktop/repositories/CompCert/ccomp -v -fstruct-return -fstruct-passing -finline-asm -O3 Poly1305_32.c kremlib.c ../../../other_providers/tweetnacl/tweetnacl.c test-poly32.c ../../../other_providers/openssl/libcrypto.a -lsodium -lkremlin -L. -I ../../../other_providers/openssl/crypto/include -I ../../../other_providers/openssl/crypto/poly1305 -I ../../../other_providers/tweetnacl -g3 -gdwarf-3
	mv a.out test-poly32-cc.exe
	./test-poly32-cc.exe

cc32_64:
	gcc-6 -O3 testlib.c -shared -o libkremlin.so -fPIC -g3 -gdwarf-3
	/usr/local/Cellar/compcert/3.0.1_1/bin/ccomp  -fpacked-structs -fstruct-passing -finline-asm -O3 Poly1305_32.c kremlib.c ../../../other_providers/tweetnacl/tweetnacl.c test-poly32.c ../../../other_providers/openssl/libcrypto.a -lsodium -lkremlin -L. -I ../../../other_providers/openssl/crypto/include -I ../../../other_providers/openssl/crypto/poly1305 -I ../../../other_providers/tweetnacl -S -g3 -gdwarf-3
	mv Poly1305_32.s Poly1305_32-cc.s
	/usr/local/Cellar/compcert/3.0.1_1/bin/ccomp  -v -fstruct-return -fstruct-passing -finline-asm -O3 Poly1305_32.c kremlib.c ../../../other_providers/tweetnacl/tweetnacl.c test-poly32.c ../../../other_providers/openssl/libcrypto.a -lsodium -lkremlin -L. -I ../../../other_providers/openssl/crypto/include -I ../../../other_providers/openssl/crypto/poly1305 -I ../../../other_providers/tweetnacl -g3 -gdwarf-3
	mv a.out test-poly32-cc.exe
	./test-poly32-cc.exe

cc32-custom:
	gcc-6 -O3 -m32 testlib.c -shared -o libkremlin.so -fPIC -g3 -gdwarf-3
	~/Desktop/repositories/CompCert/ccomp -D$(INT128) -fpacked-structs -fstruct-passing -finline-asm -O3 Poly1305_64.c kremlib.c ../../../other_providers/tweetnacl/tweetnacl.c test-poly.c ../../../other_providers/openssl/libcrypto.a -lsodium -lkremlin -L. -I ../../../other_providers/openssl/crypto/include -I ../../../other_providers/openssl/crypto/poly1305 -I ../../../other_providers/tweetnacl -S -g3 -gdwarf-3
	mv Poly1305_64.s Poly1305_32-cc.s
	~/Desktop/repositories/CompCert/ccomp -D$(INT128) -fstruct-return -fstruct-passing -finline-asm -O3 Poly1305_64.c kremlib.c ../../../other_providers/tweetnacl/tweetnacl.c test-poly.c ../../../other_providers/openssl/libcrypto.a -lsodium -lkremlin -L. -I ../../../other_providers/openssl/crypto/include -I ../../../other_providers/openssl/crypto/poly1305 -I ../../../other_providers/tweetnacl -g3 -gdwarf-3
	mv a.out test-poly32-cc.exe
	./test-poly32-cc.exe

