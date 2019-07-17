# -*- Makefile -*-

# --------------------------------------------------------------------
SUBDIRS := \
crypto_core/keccakf160064bits/ref/ \
crypto_core/keccakf160064bits/scalar/ \
crypto_core/keccakf160064bits/avx2-openssl/ \
crypto_core/keccakf160064bits/avx2/ \
\
crypto_hash/keccak1600/ref/ \
crypto_hash/keccak1600/scalar/ \
crypto_hash/keccak1600/avx2/ \
\
crypto_hash/shake128/scalar/ \
crypto_hash/shake128/avx2/ \
crypto_hash/keccak1600/scalar/ \
crypto_hash/keccak1600/avx2/ \
crypto_hash/sha3384/scalar/ \
crypto_hash/sha3384/avx2/ \
crypto_hash/shake256/ref/ \
crypto_hash/shake256/scalar/ \
crypto_hash/shake256/avx2/ \
crypto_hash/sha3256/scalar/ \
crypto_hash/sha3256/avx2/ \
crypto_hash/sha3512/scalar/ \
crypto_hash/sha3512/avx2/ \
crypto_hash/sha3224/scalar/ \
crypto_hash/sha3224/avx2/

# --------------------------------------------------------------------
.PHONY: default clean

default:
	@for i in $(SUBDIRS); do $(MAKE) -C $$i; done

clean:
	@for i in $(SUBDIRS); do $(MAKE) -C $$i clean; done
