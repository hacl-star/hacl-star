FSTAR_HOME?=../../FStar
KREMLIN_HOME?=../../kremlin
HACL_HOME?=..
include $(HACL_HOME)/lib/hyperstack/Makefile.include
SUBDIRS=symmetric ec # hash hmac hkdf
INCLUDES=$(addprefix --include , $(HACL_LIB) $(HACL_SYMMETRIC) $(HACL_EC) .)
# Sufficient modules to extract/lax-typecheck all others modules
MAIN_MODULES=Hacl.Box 
# All the directory modules (for efficient verification)
BOX_MODULES=Hacl.Box
SECRETBOX_MODULES=Hacl.SecretBox
MODULES=$(BOX_MODULES) $(SECRETBOX_MODULES)

lax: $(addsuffix .lax, $(SUBDIRS)) $(addsuffix .fst-lax, $(MAIN_MODULES))
ver: $(addsuffix .ver, $(SUBDIRS)) $(addsuffix .fst-ver, $(MODULES))

%.ver:
	$(MAKE) -C $(basename $@) ver
%.lax:
	$(MAKE) -C $(basename $@) lax

clean:
	$(MAKE) clean -C symmetric
	$(MAKE) clean -C ec
	$(MAKE) clean -C hash
	$(MAKE) clean -C hmac
	$(MAKE) clean -C hkdf
