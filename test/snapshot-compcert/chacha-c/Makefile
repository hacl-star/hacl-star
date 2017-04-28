cc:
	gcc-6 -O3 testlib.c libkremlin.c -shared -o libkremlin.so -fPIC -g3 -gdwarf-3
	/usr/local/Cellar/compcert/3.0/bin/ccomp -fpacked-structs -fstruct-passing -finline-asm -O3 Chacha20.c kremlib.c Combinators.c ../../../other_providers/openssl/libcrypto.a -lsodium -lkremlin -L. -S -g3 -gdwarf-3
	mv Chacha20.s Chacha20-cc.s
	/usr/local/Cellar/compcert/3.0/bin/ccomp -fpacked-structs -fstruct-passing -finline-asm -O3 Chacha20.c kremlib.c test-chacha.c Combinators.c ../../../other_providers/openssl/libcrypto.a -lsodium -lkremlin -L. -g3 -gdwarf-3
	mv a.out test-chacha-cc.exe
	./test-chacha-cc.exe

gcc:
	gcc-6 -O3 testlib.c -shared -o libkremlin.so -fPIC
	gcc-6 -O3 -c -S Chacha20.c -g
	mv Chacha20.s Chacha20-gcc.s
	gcc-6 -O3 Chacha20.c kremlib.c Combinators.c test-chacha.c ../../../other_providers/openssl/libcrypto.a -lsodium -lkremlin -L. -g3 -gdwarf-3
	mv a.out test-chacha-gcc.exe
	./test-chacha-gcc.exe


gcc32:
	gcc-6 -O3 -m32 testlib.c -shared -o libkremlin.so -fPIC
	gcc-6 -O3 -m32 -c -S Chacha20.c -g
	mv Chacha20.s Chacha20-gcc.s
	gcc-6 -v -O3 -m32 -mtune=generic Chacha20.c kremlib.c Combinators.c test-chacha.c -lkremlin -L. -g3 -gdwarf-3
	mv a.out test-chacha-gcc32.exe
	./test-chacha-gcc32.exe

