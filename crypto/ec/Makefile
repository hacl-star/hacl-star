all:
	@echo
	@echo "############## LAX TYPECHEKING #############"
	@echo
	$(MAKE) lax
	@echo
	@echo "############## FULL TYPECHEKING #############"
	@echo
	$(MAKE) ver

FSTAR_HOME?=../../../FStar
KREMLIN_HOME=$(FSTAR_HOME)/../kremlin
HACL_HOME=../..
include ../../lib/hyperstack/Makefile.include

MODULES=Hacl.EC.Curve25519.Parameters \
	Hacl.EC.Curve25519.Bigint \
	Hacl.EC.Curve25519.Utils \
	Hacl.EC.Curve25519.Bignum.Fdifference \
	Hacl.EC.Curve25519.Bignum.Fproduct \
	Hacl.EC.Curve25519.Bignum.Fscalar \
	Hacl.EC.Curve25519.Bignum.Fsum \
	Hacl.EC.Curve25519.Bignum.Modulo \
	Hacl.EC.Curve25519.Bignum \
	Hacl.EC.Curve25519.Crecip \
	Hacl.EC.Curve25519.PPoint \
	Hacl.EC.Curve25519.AddAndDouble \
	Hacl.EC.Curve25519.Ladder \
	Hacl.EC.Curve25519

FSTAR_INCLUDES:=-I ../../lib/hyperstack

%.fst-ver-ct: %.fst
	$(FSTAR) $(FSTAR_OPTIONS_VER) $(FSTAR_INCLUDES) $^
%.fst-lax-ct: %.fst
	$(FSTAR) $(FSTAR_OPTIONS_VER) $(FSTAR_INCLUDES) $^ -fsopt "--lax"

ver: $(addsuffix .fst-ver-ct, $(MODULES))
lax: $(addsuffix .fst-lax-ct, $(MODULES))

clean:
	rm -f *~
