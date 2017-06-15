cc:
	gcc-6 -O3 testlib.c libkremlin.c -shared -o libkremlin.so -fPIC -g3 -gdwarf-3
	/usr/local/Cellar/compcert/3.0.1_1/bin/ccomp -D$(INT128) -fpacked-structs -fstruct-passing -finline-asm -O3 Curve25519.c kremlib.c ../../../other_providers/tweetnacl/tweetnacl.c test-curve.c ../../../other_providers/openssl/libcrypto.a ../../../other_providers/openssl/libssl.a -lsodium -lkremlin -L. -I ../../../other_providers/openssl/crypto/ec -I ../../../other_providers/openssl -I ../../../other_providers/openssl/include -I ../../../other_providers/tweetnacl -S -g3 -gdwarf-3
	mv Curve25519.s Curve25519-cc.s
	/usr/local/Cellar/compcert/3.0.1_1/bin/ccomp -D$(INT128) -fpacked-structs -fstruct-passing -finline-asm -O3 Curve25519.c kremlib.c ../../../other_providers/tweetnacl/tweetnacl.c test-curve.c ../../../other_providers/openssl/libcrypto.a ../../../other_providers/openssl/libssl.a -lsodium -lkremlin -L. -I ../../../other_providers/openssl/crypto/ec -I ../../../other_providers/openssl -I ../../../other_providers/openssl/include -I ../../../other_providers/tweetnacl -g3 -gdwarf-3
	mv a.out test-curve-cc.exe
	./test-curve-cc.exe

gcc:
	gcc-6 -O3 testlib.c libkremlin.c -shared -o libkremlin.so -fPIC
	gcc-6 -D$(INT128) -O3 -c -S Curve25519.c -g
	mv Curve25519.s Curve25519-gcc.s
	gcc-6 -mtune=native -D$(INT128) -v -O3 Curve25519.c kremlib.c ../../../other_providers/tweetnacl/tweetnacl.c test-curve.c ../../../other_providers/openssl/libcrypto.a -lsodium -lkremlin -L. -I ../../../other_providers/openssl/include -I ../../../other_providers/openssl -I ../../../other_providers/openssl/crypto/ec -I ../../../other_providers/tweetnacl -g
	mv a.out test-curve-gcc.exe
	./test-curve-gcc.exe


gcc32:
	gcc-6 -O3 -m32 testlib.c -shared -o libkremlin.so -fPIC
	gcc-6 -D$(INT128) -O3 -m32 -c -S Curve25519.c -g
	mv Curve25519.s Curve25519-gcc.s
	gcc-6 -D$(INT128) -v -O3 -m32 -mtune=generic Curve25519.c kremlib.c ../../../other_providers/tweetnacl/tweetnacl.c test-curve.c ../../../other_providers/openssl/libcrypto.a -lsodium -lkremlin -L. -I ../../../other_providers/openssl/include -I ../../../other_providers/openssl -I ../../../other_providers/openssl/crypto/ec -I ../../../other_providers/tweetnacl -g
	mv a.out test-curve-gcc32.exe
	./test-curve-gcc32.exe


cc32:
	gcc-6 -O3 -m32 testlib.c -shared -o libkremlin.so -fPIC
	~/Desktop/repositories/CompCert/ccomp -D$(INT128) -fpacked-structs -fstruct-passing -finline-asm -O3 Curve25519.c kremlib.c ../../../other_providers/tweetnacl/tweetnacl.c test-curve.c ../../../other_providers/openssl/libcrypto.a ../../../other_providers/openssl/libssl.a -lsodium -lkremlin -L. -I ../../../other_providers/openssl/crypto/ec -I ../../../other_providers/openssl -I ../../../other_providers/openssl/include -I ../../../other_providers/tweetnacl -g3 -gdwarf-3 -S
	mv Curve25519.s Curve25519-ccc.s
	~/Desktop/repositories/CompCert/ccomp -D$(INT128) -fpacked-structs -fstruct-passing -finline-asm -O3 Curve25519.c kremlib.c ../../../other_providers/tweetnacl/tweetnacl.c test-curve.c ../../../other_providers/openssl/libcrypto.a ../../../other_providers/openssl/libssl.a -lsodium -lkremlin -L. -I ../../../other_providers/openssl/crypto/ec -I ../../../other_providers/openssl -I ../../../other_providers/openssl/include -I ../../../other_providers/tweetnacl -g3 -gdwarf-3 
	mv a.out test-curve-cc32.exe
	./test-curve-cc32.exe



