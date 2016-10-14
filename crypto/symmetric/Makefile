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
MAIN_MODULES=Hacl.Symmetric.XSalsa20 \
	Hacl.AEAD.Chacha20Poly1305 \
	Hacl.AEAD.AES256GCM \

# All the directory modules (for efficient verification)
POLY1305_MODULES=$(addprefix Hacl.Symmetric.Poly1305., Parameters Bigint Bignum) \
	Hacl.Symmetric.Poly1305
COMMON_MODULES=Utils
CHACHA20_MODULES=Hacl.Symmetric.Chacha20
SALSA20_MODULES=Hacl.Symmetric.Salsa20
XSALSA20_MODULES=Hacl.Symmetric.XSalsa20
MODULES=$(COMMON_MODULES) $(CHACHA20_MODULES) $(SALSA20_MODULES) $(XSALSA20_MODULES) \
	$(POLY1305_MODULES)

lax: $(addsuffix .fst-lax, $(MAIN_MODULES))
ver: $(addsuffix .fst-ver, $(MODULES))

clean:
	rm -f *~ $(addprefix ml/, *.cmo *.cmi *.o *~ *.cmx) $(HACL_FILES)
