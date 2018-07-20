include ../../Makefile.include

API_FILES= \
	Hacl.Constants.fst \
	Hacl.Chacha20Poly1305.fst \
	Hacl.SecretBox.ZeroPad.fst \
	Hacl.Box.ZeroPad.fst \
	Hacl.Box.fst \
	NaCl.fst

INCLUDE_DIRS=../salsa-family $(HACL_HOME)/code/bignum ../curve25519 ../curve25519/interfaces ../poly1305 ../hash
FSTAR_INCLUDES+=$(addprefix --include ,$(INCLUDE_DIRS))


# Parameter for interactive mode
%.fst-in:
	@echo $(OPTIONS) --hint_info \
	$(FSTAR_INCLUDES)

ct: $(addsuffix -lax, $(API_FILES))
verify: $(addsuffix -verify, $(API_FILES))
hints: $(addsuffix .hints, $(API_FILES))
all-ver: verify
all-ct: ct
all-hints: hints

# For CI, all modules restricted from incomplete or slow ones
all-ci: $(addsuffix -verify, $(filter-out $(SLOW) $(TODO), $(API_FILES)))

api: verify

extract-c: aead-c/Hacl_Chacha20Poly1305.c box-c/NaCl.c policies-c/Hacl_Policies.c

test:

KREMLIN_ARGS+=$(addprefix -I ,$(INCLUDE_DIRS)) \
	-drop Prims,LowStar,C.Loops.Spec.Loops,Spec.*,Hacl.Spec.*,Hacl.Spe.*,Hacl.Impl.*,Seq.*,Hacl.Constants,Hacl.Endianness \
	-drop Hacl.UInt8,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128,Hacl.Cast,Hacl.UInt16,Hacl.Types

policies-c/Hacl_Policies.c: $(HACL_HOME)/code/lib/kremlin/Hacl.Policies.fst
	$(KREMLIN) $(KREMLIN_ARGS) $^ -tmpdir policies-c -skip-compilation -minimal -bundle Hacl_Policies=* -add-include '"kremlib.h"'

box-c/NaCl.c: $(HACL_HOME)/code/poly1305/Hacl.Poly1305_64.fsti $(HACL_HOME)/code/salsa-family/Hacl.Salsa20.fsti $(HACL_HOME)/code/curve25519/interfaces/Hacl.Curve25519.fsti Hacl.SecretBox.ZeroPad.fst Hacl.Box.ZeroPad.fst  NaCl.fst
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir box-c NaCl.fst -skip-compilation \
		-bundle "NaCl=*" -minimal -add-include '"kremlib.h"' \
		-library "Hacl.Policies"

aead-c/Hacl_Chacha20Poly1305.c: $(HACL_HOME)/code/poly1305/AEAD.Poly1305_64.fsti $(HACL_HOME)/code/salsa-family/Hacl.Chacha20.fsti Hacl.Chacha20Poly1305.fst
	$(KREMLIN) $(KREMLIN_ARGS) -I interfaces -tmpdir aead-c Hacl.Chacha20Poly1305.fst -skip-compilation \
	-add-include '"Hacl_Chacha20.h"' -add-include '"AEAD_Poly1305_64.h"' \
	-minimal -add-include '"kremlib.h"' -bundle 'Hacl.Chacha20Poly1305=*' \
	# TODO: FIX FOR KREMLIN EXTRACTION ISSUE, CHECK WITH JP
	$(SED) -i 's/(void \*)(uint8_t)0U, //g' aead-c/Hacl_Chacha20Poly1305.c

count-line:
	@echo "LOC for AEAD CHACHAPOLY"
	cloc --force-lang=ocaml Hacl.Chacha20Poly1305.fst
	@echo "LOC for SECRETBOX"
	cloc --force-lang=ocaml Hacl.SecretBox.ZeroPad.fst
	@echo "LOC for BOX"
	cloc --force-lang=ocaml Hacl.Box.ZeroPad.fst

clean:
	rm -rf api-c *~ *.exe *.graph *.o *.out aead-c box-c policies-c

ifeq ($(UNAME),Darwin)
  SED=gsed
else
  SED=sed
endif
