This directory contains several OpenSSL engines suitable for the `speed` command.
- HaclEngine.dll (or .so): implements x25519 using the HACL* implementation.
- OpenSSLEngine.dll (or .so): implements x25519 using the original OpenSSL
  implementation; this is to make sure we're pitting HACL* against the OpenSSL
  implementation including the same overhead of going through an external
  engine.
- BCryptEngine.dll (windows-only): runs the x25519 multiplication using Windows
  10 SDK's BCrypt/CNG functions.

Use as follows:
- checkout openssl and compile it (using `CC=x86_64-w64-mingw32-gcc ./Configure
  mingw64` on Windows);
- possibly overriding OPENSSL_HOME and KREMLIN_HOME, run `make` followed by one
  of the three targets above;
- run `$OPENSSL_HOME/apps/openssl`, possibly prefixed by
  `DYLD_LIBRARY_PATH=$OPENSSL_HOME` on OSX, `PATH=...` on Windows and
  `LD_LIBRARY_PATH=...` on Linux.

Sample session:

```
jonathan@chartreuse:~/Code/hacl-star/test/openssl-engine (protz_) $ DYLD_LIBRARY_PATH=../../../openssl/ rlwrap ../../../openssl/apps/openssl
OpenSSL> engine /Users/jonathan/Code/hacl-star/test/openssl-engine/haclengine.so
(/Users/jonathan/Code/hacl-star/test/openssl-engine/haclengine.so) Everest engine (HACL* crypto)
Loaded: (Everest) Everest engine (HACL* crypto)
OpenSSL> speed -engine Everest ecdhx25519
engine "Everest" set.
Doing 253 bit  ecdh's for 10s: 142752 253-bit ECDH ops in 9.97s
...
```

Note the use of an absolute path to locate the `.so` and the `-engine Everest`
flag for the `speed` command.
