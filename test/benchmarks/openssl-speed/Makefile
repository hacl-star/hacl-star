prepare:
	git clone https://github.com/openssl/openssl.git
	cd openssl;  CC=gcc-6 ./config; make; cd ..
	cp openssl/apps/openssl openssl/apps/openssl-old

hacl-speed: openssl
	cat ../../snapshots/hacl-c/Curve25519.c hacl-curve25519.c > openssl/crypto/ec/curve25519.c
	cp ../../snapshots/hacl-c/Curve25519.h openssl/crypto/ec/
	cp ../../snapshots/hacl-c/kremlib.h openssl/crypto/ec/
	cd openssl;  CC=gcc-6 ./config; make; cd ..
	cp openssl/apps/openssl openssl/apps/openssl-new
	openssl/apps/openssl-old speed ecdhx25519
	openssl/apps/openssl-new speed ecdhx25519

