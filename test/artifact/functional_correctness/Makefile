FSTAR_HOME?=../../FStar
KREMLIN_HOME?=$(FSTAR_HOME)../kremlin
HACL_HOME?=../../..
include $(HACL_HOME)/lib/hyperstack/Makefile.include

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

MODULES=$(CURVE25519_MODULES)

ver: $(addsuffix .fst-ver, $(MODULES))
hints: $(addsuffix .fst-hints, $(MODULES))

%.fst-hints: %.fst
	$(FSTAR) $(FSTAR_OPTIONS_VER) $(INCLUDES) --verify_module $(basename $(notdir $@)) $^ --record_hints

clean:
	rm -f *~
