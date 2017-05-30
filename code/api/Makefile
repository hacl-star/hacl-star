include ../Makefile.include

API_FILES= \
	Hacl.Constants.fst \
	Chacha20Poly1305.fst \
	Hacl.SecretBox.ZeroPad.fst \
	Hacl.Box.ZeroPad.fst

FSTAR_INCLUDE_PATHS=--include $(FSTAR_HOME)/ulib/hyperstack --include ../lib/kremlin --include ../../specs --include $(FSTAR_HOME)/../kremlin/kremlib

FSTARB=$(FSTAR_BASE) \
		--include ../lib/kremlin --include ../salsa-family --include $(HACL_HOME)/code/bignum --include ../curve25519 \
		--include ../poly1305 --include ../../specs \
		--include $(KREMLIN_HOME)/kremlib $(HINTS_ENABLED) $(OTHERFLAGS)

FSTAR_CT=$(FSTAR_BASE) \
		--include ../lib/ --include ../salsa-family --include ../bignum --include ../curve25519 \
		--include ../poly1305 --include ../../specs \
		--include $(KREMLIN_HOME)/kremlib $(HINTS_ENABLED) $(OTHERFLAGS)

KRML=$(KREMLIN_HOME)/krml -I ../lib/kremlin -I ../salsa-family -I ../curve25519 \
		-I ../poly1305 -I ../../specs -I $(HACL_HOME)/code/bignum  \
		-drop FStar -drop Hacl.Spec -drop Prims -drop Hacl.Cast -drop Hacl.UInt8 \
		-drop Hacl.UInt16 -drop Hacl.UInt32 -drop Hacl.UInt64 -drop Hacl.UInt128 \
		-drop Hacl.Types $(KREMLIN_ARGS)

KRML2=$(KREMLIN_HOME)/krml -I ../lib/kremlin -I ../salsa-family -I ../curve25519 \
		-I ../poly1305 -I ../../specs -I $(HACL_HOME)/code/bignum \
		-drop FStar,Hacl.Spec,Prims,Hacl.Cast,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64 \
		-drop Hacl.UInt128,Hacl.Types $(KREMLIN_ARGS)

# Lax typechecking against the restricted integer interface
%.fst-ct: %.fst
	$(FSTAR_CT) --lax $^

all-ct:
	$(FSTAR_CT) --lax $(API_FILES)
# Parameter for interactive mode
%.fst-in:
	@echo $(OPTIONS) --hint_info \
	$(FSTAR_INCLUDE_PATHS)

# Full typechecking against the transparent integer interface
%.fst-verify: %.fst
	$(FSTARB) $^

all-ver: $(addsuffix -verify, $(API_FILES))

# Minimal lax typechecking, pre-requisite to any extraction
%.fst-lax: %.fst
	$(FSTARB) --lax $^

all-lax: $(addsuffix -lax, $(API_FILES))

# Hints regeneration
%.fst-hints: %.fst
	-$(FSTARB) --record_hints $^

all-hints: $(addsuffix -hints, $(API_FILES))

# For CI, all modules restricted from incomplete or slow ones
all-ci: $(addsuffix -verify, $(filter-out $(SLOW) $(TODO), $(API_FILES)))

api: verify

extract-c: box-c/NaCl.c aead-c/Chacha20Poly1305.c

# Legacy, to be removed
extract-api:
	mkdir -p api-c
	$(KRML) -tmpdir api-c NaCl.fst -verbose -skip-compilation \
		$(addprefix -drop , 'Spec.\*' 'Hacl.Spec.\*' 'Hacl.Spe.\*' 'Hacl.Impl.\*' "Seq.\*" \
				    Hacl.Constants Hacl.Endianness) \
		-bundle "NaCl=NaCl,Hacl.SecretBox,Hacl.Box"

box-c/NaCl.c: $(HACL_HOME)/code/poly1305/Poly1305_64.fsti $(HACL_HOME)/code/salsa-family/Salsa20.fsti $(HACL_HOME)/code/curve25519/Curve25519.fsti Hacl.SecretBox.ZeroPad.fst Hacl.Box.ZeroPad.fst NaCl.fst
	mkdir -p box-c
	$(KRML) -tmpdir box-c NaCl.fst -skip-compilation \
		$(addprefix -drop , 'Spec.\*' 'Hacl.Spec.\*' 'Hacl.Spe.\*' 'Hacl.Impl.\*' "Seq.\*" \
				    Hacl.Constants Hacl.Endianness) \
		-bundle "NaCl=NaCl,Hacl.SecretBox.ZeroPad,Hacl.Box.ZeroPad"

aead-c/Chacha20Poly1305.c: $(HACL_HOME)/code/poly1305/AEAD.Poly1305_64.fsti $(HACL_HOME)/code/salsa-family/Chacha20.fsti Chacha20Poly1305.fst
	mkdir -p aead-c
	$(KRML2) -tmpdir aead-c Chacha20Poly1305.fst \
		-drop Hacl.Bignum.Constants,Hacl.Bignum.Parameters,Hacl.Bignum.Limb,Hacl.Bignum.Wide \
		-drop Hacl.UInt16,Hacl.Types,Spec.\*,Hacl.Spec.\*,Hacl.Spe.\* \
		-drop Hacl.Constants,Hacl.Endianness,Hacl.Bignum.\*,Hacl.Spe.\*,Seq.\*,Hacl.Impl.\* \
		-drop AEAD_Poly1305_64,Chacha20 \
		-add-include '"testlib.h"' -skip-compilation -add-include '"Chacha20.h"' \
		-add-include '"AEAD_Poly1305_64.h"' -I ../salsa-family -I ../poly1305 -I ../bignum -I ../../specs
	# TODO: FIX FOR KREMLIN EXTRACTION ISSUE, CHECK WITH JP
	sed -i 's/(void \*)(uint8_t )0, //g' aead-c/Chacha20Poly1305.c

count-line:
	@echo "LOC for AEAD CHACHAPOLY"
	cloc --force-lang=ocaml Chacha20Poly1305.fst
	@echo "LOC for SECRETBOX"
	cloc --force-lang=ocaml Hacl.SecretBox.ZeroPad.fst
	@echo "LOC for BOX"
	cloc --force-lang=ocaml Hacl.Box.ZeroPad.fst

clean:
	rm -rf api-c *~ *.exe *.graph *.o *.out aead-c box-c
