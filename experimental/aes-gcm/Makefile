all:
	@echo
	@echo "############## LAX TYPECHEKING #############"
	@echo
	$(MAKE) lax
	@echo
	@echo "############## FULL TYPECHEKING #############"
	@echo
	$(MAKE) ver

FSTAR_HOME ?= ../../../FStar
FSTAR ?= $(FSTAR_HOME)/bin/fstar.exe 
KREMLIN_HOME = $(FSTAR_HOME)/../kremlin
HACL_HOME ?= ../..

MODULES= Hacl.Symmetric.GCM.fst Hacl.Symmetric.AES.fst Hacl.AEAD.AES256GCM.fst

FSTAR_INCLUDES:=--include $(FSTAR_HOME)/ulib/hyperstack --include $(HACL_HOME)/code/lib

lax:
	$(FSTAR) $(FSTAR_INCLUDES) --lax $(MODULES)

ver:
	$(FSTAR) $(FSTAR_INCLUDES) $(MODULES)

clean:
	rm -f *~
