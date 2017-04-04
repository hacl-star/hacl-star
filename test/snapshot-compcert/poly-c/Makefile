cc:
	gcc-6 -O3 testlib.c libkremlin.c -shared -o libkremlin.so -fPIC -g3 -gdwarf-3
	/usr/local/Cellar/compcert/3.0/bin/ccomp -fpacked-structs -fstruct-passing -finline-asm -O3 Poly1305_64.c kremlib.c ../../../other_providers/tweetnacl/tweetnacl.c test-poly.c ../../../other_providers/openssl/libcrypto.a -lsodium -lkremlin -L. -I ../../../other_providers/openssl/crypto/include -I ../../../other_providers/openssl/crypto/poly1305 -I ../../../other_providers/tweetnacl -S -g3 -gdwarf-3
	mv Poly1305_64.s Poly1305_64-cc.s
	/usr/local/Cellar/compcert/3.0/bin/ccomp -v -fstruct-return -fstruct-passing -finline-asm -O3 Poly1305_64.c kremlib.c ../../../other_providers/tweetnacl/tweetnacl.c test-poly.c ../../../other_providers/openssl/libcrypto.a -lsodium -lkremlin -L. -I ../../../other_providers/openssl/crypto/include -I ../../../other_providers/openssl/crypto/poly1305 -I ../../../other_providers/tweetnacl -g3 -gdwarf-3
	mv a.out test-poly-cc.exe
	./test-poly-cc.exe

gcc:
	gcc-6 -O3 testlib.c libkremlin.c -shared -o libkremlin.so -fPIC
	gcc-6 -O3 -c -S Poly1305_64.c -g
	mv Poly1305_64.s Poly1305_64-gcc.s
	gcc-6 -v -O3 Poly1305_64.c kremlib.c ../../../other_providers/tweetnacl/tweetnacl.c test-poly.c ../../../other_providers/openssl/libcrypto.a -lsodium -lkremlin -L. -I ../../../other_providers/openssl/crypto/include -I ../../../other_providers/openssl/crypto/poly1305 -I ../../../other_providers/tweetnacl -g
	mv a.out test-poly-gcc.exe
	./test-poly-gcc.exe

