FSTAR_HOME?=../../FStar
KREMLIN_HOME?=$(FSTAR_HOME)../kremlin
ARTIFACT_HOME=..
include $(ARTIFACT_HOME)/Makefile.include

INCLUDES=$(addprefix --include , ../lib)

# All the directory modules (for efficient verification)
CURVE25519_MODULES= \
	Hacl.EC.Curve25519.Parameters \
	Hacl.EC.Curve25519.Bigint \
	Hacl.EC.Curve25519.Utils \
	Hacl.EC.Curve25519.Bignum.Fdifference.Lemmas \
	Hacl.EC.Curve25519.Bignum.Fdifference \
	Hacl.EC.Curve25519.Bignum.Fproduct.Lemmas \
	Hacl.EC.Curve25519.Bignum.Fproduct \
	Hacl.EC.Curve25519.Bignum.Fscalar.Lemmas \
	Hacl.EC.Curve25519.Bignum.Fscalar \
	Hacl.EC.Curve25519.Bignum.Fsum.Lemmas \
	Hacl.EC.Curve25519.Bignum.Fsum \
	Hacl.EC.Curve25519.Bignum.Modulo.Lemmas \
	Hacl.EC.Curve25519.Bignum.Modulo.Lemmas2 \
	Hacl.EC.Curve25519.Bignum.Modulo.Lemmas3 \
	Hacl.EC.Curve25519.Bignum.Modulo \
	Hacl.EC.Curve25519.Bignum.Lemmas.Utils \
	Hacl.EC.Curve25519.Bignum

POLY1305_BIGNUM_MODULES= \
	Crypto.Symmetric.Poly1305.Parameters \
	Crypto.Symmetric.Poly1305.Bigint \
	Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part1 \
	Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part2 \
	Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part3 \
	Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part4 \
	Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part5 \
	Crypto.Symmetric.Poly1305.Bignum.Lemmas.Part6 \
	Crypto.Symmetric.Poly1305.Bignum

MODULES=$(CURVE25519_MODULES)

curve25519-ver: $(addsuffix .fst-ver-ct, $(CURVE25519_MODULES))
poly1305-ver: poly1305-bignum-ver
poly1305-bignum-ver: $(addsuffix .fst-ver-ct, $(POLY1305_MODULES))

hints: $(addsuffix .fst-hints, $(POLY1305_BIGNUM_MODULES))

%.fst-hints: %.fst
	$(FSTAR) $(FSTAR_OPTIONS_VER) $(INCLUDES) --verify_module $(basename $(notdir $@)) $^ --record_hints --include $(LIB)

clean:
	rm -f *~
