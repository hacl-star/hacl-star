all:
	@echo
	@echo "############## LAX TYPECHEKING #############"
	@echo
	$(MAKE) lax
	@echo
	@echo "############## FULL TYPECHEKING #############"
	@echo
	$(MAKE) ver

FSTAR_HOME?=../../FStar
KREMLIN_HOME?=../../kremlin
HACL_HOME?=../..
include $(HACL_HOME)/lib/hyperstack/Makefile.include

INCLUDES=$(addprefix --include , $(HACL_LIB) $(HACL_SYMMETRIC))

# Sufficient modules to extract/lax-typecheck all others modules
MAIN_MODULES=Hacl.EC.Curve25519

# All the directory modules (for efficient verification)
CURVE25519_MODULES=$(addprefix Hacl.EC.Curve25519., Parameters Bigint Bignum.Fsum Bignum.FsumWide \
		Bignum.Fdifference Bignum.Fscalar Bignum.Fproduct Bignum.Modulo Bignum \
		Crecip PPoint AddAndDouble Ladder) \
	Hacl.EC.Curve25519

MODULES=$(CURVE25519_MODULES)

lax: $(addsuffix .fst-lax, $(MAIN_MODULES))
ver: $(addsuffix .fst-ver, $(MODULES))

clean:
	rm -f *~ $(addprefix ml/, *.cmo *.cmi *.o *~ *.cmx) $(HACL_FILES)
