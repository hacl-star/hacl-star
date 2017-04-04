cc:
	gcc-6 -O3 testlib.c libkremlin.c -shared -o libkremlin.so -fPIC -g3 -gdwarf-3
	/usr/local/Cellar/compcert/3.0/bin/ccomp -fpacked-structs -fstruct-passing -finline-asm -O3 Curve25519.c kremlib.c ../../../other_providers/tweetnacl/tweetnacl.c test-curve.c ../../../other_providers/openssl/libcrypto.a ../../../other_providers/openssl/libssl.a -lsodium -lkremlin -L. -I ../../../other_providers/openssl/crypto/ec -I ../../../other_providers/openssl -I ../../../other_providers/openssl/include -I ../../../other_providers/tweetnacl -S -g3 -gdwarf-3
	mv Curve25519.s Curve25519-cc.s
	/usr/local/Cellar/compcert/3.0/bin/ccomp -fpacked-structs -fstruct-passing -finline-asm -O3 Curve25519.c kremlib.c ../../../other_providers/tweetnacl/tweetnacl.c test-curve.c ../../../other_providers/openssl/libcrypto.a ../../../other_providers/openssl/libssl.a -lsodium -lkremlin -L. -I ../../../other_providers/openssl/crypto/ec -I ../../../other_providers/openssl -I ../../../other_providers/openssl/include -I ../../../other_providers/tweetnacl -g3 -gdwarf-3
	mv a.out test-curve-cc.exe
	./test-curve-cc.exe

gcc:
	gcc-6 -O3 testlib.c libkremlin.c -shared -o libkremlin.so -fPIC
	gcc-6 -O3 -c -S Curve25519.c -g
	mv Curve25519.s Curve25519-gcc.s
	gcc-6 -v -O3 Curve25519.c kremlib.c ../../../other_providers/tweetnacl/tweetnacl.c test-curve.c ../../../other_providers/openssl/libcrypto.a -lsodium -lkremlin -L. -I ../../../other_providers/openssl/include -I ../../../other_providers/openssl -I ../../../other_providers/openssl/crypto/ec -I ../../../other_providers/tweetnacl -g
	mv a.out test-curve-gcc.exe
	./test-curve-gcc.exe

