include ../../../Makefile.include

all:
	@echo
	@echo "############## LAX TYPECHEKING #############"
	@echo
	$(MAKE) lax
	@echo
	@echo "############## FULL TYPECHEKING #############"
	@echo
	$(MAKE) ver

SLOW=
BROKEN=

AESGCM_FILES=Hacl.Symmetric.GCM.fst ../aesgcm/Hacl.Symmetric.AES.fst Hacl.AEAD.AES256GCM.fst

INCLUDE_DIRS=$(HACL_HOME)/code/lib/kremlin $(HACL_HOME)/code/experimental/aesgcm .

FSTAR_INCLUDES+=$(addprefix --include , $(INCLUDE_DIRS))

ci: $(addsuffix -verify, $(filter-out $(SLOW) $(BROKEN), $(AESGCM_FILES)))
ct: $(addsuffix -lax, $(AESGCM_FILES))
verify: $(addsuffix -verify, $(AESGCM_FILES))
hints: $(addsuffix .hints, $(filter-out $(BROKEN), $(AESGCM_FILES)))

all-ci: ci
all-ct: ct
all-ver: verify
all-hints: hints

clean:
	rm -f *~
