include ../code/Makefile.include

all:
	@echo
	@echo "############## LAX TYPECHEKING #############"
	@echo
	$(MAKE) lax
	@echo
	@echo "############## FULL TYPECHEKING #############"
	@echo
	$(MAKE) ver

MODULES=Hacl.Symmetric.GCM.fst Hacl.Symmetric.AES.fst Hacl.AEAD.AES256GCM.fst

FSTAR_INCLUDES+=--include $(HACL_HOME)/code/lib

lax:
	$(FSTAR) --lax $(MODULES)

ver:
	$(FSTAR) $(MODULES)

clean:
	rm -f *~
