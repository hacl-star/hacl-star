Compiling just the OpenSSL/HACL* engines:

x86_64-w64-mingw32-gcc -I../../../openssl/include -L../../../openssl   -I../../../kremlin/kremlib -shared -o haclengine.dll HACLEngine.c -I../../code/curve25519/x25519-c -Wall -lcrypto ../../code/curve25519/x25519-c/Curve25519.c -Wno-unused-variable -Wno-parentheses -DIMPL=IMPL_HACL -O3 -flto

For Windows...

cl /c /FoBCryptWrapper.o /I"c:/Program Files (x86)/Windows Kits/10/Include/10.0.14393.0/shared" BCryptWrapper.c
x86_64-w64-mingw32-gcc -I../../../openssl/include -L../../../openssl   -I../../../kremlin/kremlib -I../../code/curve25519/x25519-c -Wall -lcrypto ../../code/curve25519/x25519-c/Curve25519.c -Wno-unused-variable -Wno-parentheses -DIMPL=IMPL_BCRYPT -O3 HACLEngine.c BCryptWrapper.o -lbcrypt -lcrypto -shared -o EverestBCrypt.dll

Issues with the wrong version of msvcrt.

x86_64-w64-mingw32-gcc -I../../../openssl/include -L../../../openssl   -I../../../kremlin/kremlib -I../../code/curve25519/x25519-c -Wall -lcrypto ../../code/curve25519/x25519-c/Curve25519.c -Wno-unused-variable -Wno-parentheses -DIMPL=IMPL_BCRYPT -O3 HACLEngine.c BCryptWrapper.c -lbcrypt -lcrypto -shared -o EverestBCrypt.dll
