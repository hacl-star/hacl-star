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

MODULES=Hacl.Symmetric.Poly1305_64.Parameters \
	Hacl.Symmetric.Poly1305_64.Bigint \
	Hacl.Symmetric.Poly1305_64 \
	Hacl.Symmetric.HSalsa20 \
	Hacl.Symmetric.Salsa20 \
	Hacl.Symmetric.XSalsa20

FSTAR_INCLUDES:=-I ../../lib/hyperstack

%.fst-ver-ct: %.fst
	$(FSTAR) $(FSTAR_OPTIONS_VER) $(FSTAR_INCLUDES) $^
%.fst-lax-ct: %.fst
	$(FSTAR) $(FSTAR_OPTIONS_VER) $(FSTAR_INCLUDES) $^ -fsopt "--lax"

ver: $(addsuffix .fst-ver-ct, $(MODULES))
lax: $(addsuffix .fst-lax-ct, $(MODULES))

clean:
	rm -f *~
