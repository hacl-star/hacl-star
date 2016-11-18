all: symmetric-ver ec-ver
	@echo
	@echo "############## LAX TYPECHEKING #############"
	@echo
	$(MAKE) lax
	@echo
	@echo "############## FULL TYPECHEKING #############"
	@echo
	$(MAKE) ver

FSTAR_HOME?=../../FStar
KREMLIN_HOME=$(FSTAR_HOME)/../kremlin
HACL_HOME=..
include ../lib/hyperstack/Makefile.include

SUBDIRS=symmetric ec
INCLUDES=$(addprefix --include , $(HACL_LIB) $(HACL_SYMMETRIC) $(HACL_EC) .)

MODULES=Hacl.SecretBox \
	Hacl.Box

FSTAR_INCLUDES:=-I ../lib/hyperstack -I ec -I symmetric

%.fst-ver-ct: %.fst
	$(FSTAR) $(FSTAR_OPTIONS_VER) $(FSTAR_INCLUDES) $^
%.fst-lax-ct: %.fst
	$(FSTAR) $(FSTAR_OPTIONS_VER) $(FSTAR_INCLUDES) $^ -fsopt "--lax"

ver: $(addsuffix .fst-ver-ct, $(MODULES))
lax: $(addsuffix .fst-lax-ct, $(MODULES))

symmetric-ver:
	$(MAKE) -C symmetric ver

ec-ver:
	$(MAKE) -C ec ver

clean:
	rm -f *~
	$(MAKE) clean -C symmetric
	$(MAKE) clean -C ec
	$(MAKE) clean -C hash
	$(MAKE) clean -C hmac
	$(MAKE) clean -C hkdf
