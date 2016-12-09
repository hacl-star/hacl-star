FSTAR_HOME?=../../FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
HACL_HOME=../..
include ../../lib/hyperstack/Makefile.include

# All the directory modules
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

INCLUDES=$(addprefix -I , $(HACL_LIB))


%.fst-lax-ct: %.fst
	$(FSTAR) $(FSTAR_OPTIONS_VER) $(INCLUDES) $^ -fsopt "--lax"

%.fst-ver-ct: %.fst
	$(FSTAR) $(FSTAR_OPTIONS_VER) $(INCLUDES) $^

curve25519-ver: $(addsuffix .fst-ver-ct, $(CURVE25519_MODULES))
curve25519-lax: Hacl.EC.Curve25519.Bignum.fst-lax-ct #$(addsuffix .fst-lax-ct, $(CURVE25519_MODULES))

poly1305-ver: $(addsuffix .fst-ver-ct, $(POLY1305_BIGNUM_MODULES))
poly1305-lax: Crypto.Symmetric.Poly1305.Bignum.fst-lax-ct  #$(addsuffix .fst-lax-ct, $(POLY1305_BIGNUM_MODULES))

ver: curve25519-ver poly1305-ver
lax: curve25519-lax poly1305-lax

clean:
	rm -f *~
