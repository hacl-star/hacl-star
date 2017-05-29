FSTAR_HOME?=../../dependencies/FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
HACL_HOME?=../..
include ../Makefile.include

API_FILES= \
	Hacl.Constants.fst \
	Chacha20Poly1305.fst \
	Hacl.SecretBox.ZeroPad.fst \
	Hacl.Box.ZeroPad.fst
#	Hacl.SecretBox.fst \
	Hacl.Box.fst

FSTARB=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib/kremlin --include ../salsa-family --include ../curve25519 \
		--include ../poly1305 --include ../../specs --include $(HACL_HOME)/code/bignum \
		--include $(KREMLIN_HOME)/kremlib

FSTAR_CT=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib/ --include ../salsa-family --include ../curve25519 \
		--include ../poly1305 --include ../../specs  --include $(HACL_HOME)/code/bignum  \
		--include $(KREMLIN_HOME)/kremlib

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

# Full typechecking against the transparent integer interface
%.fst-verify: %.fst
	$(FSTARB) $^ --use_hints --record_hints

all-ver: $(addsuffix -verify, $(API_FILES))

# Minimal lax typechecking, pre-requisite to any extraction
%.fst-lax: %.fst
	$(FSTARB) --lax $^

all-lax: $(addsuffix -lax, $(API_FILES))

# Hints regeneration
%.fst-hints: %.fst
	-$(FSTARB) $^ --use_hints --record_hints

all-hints: $(addsuffix -hints, $(API_FILES))

# For CI, all modules restricted from incomplete or slow ones
all-ci: $(addsuffix -verify, $(filter-out $(SLOW) $(TODO), $(API_FILES)))

api: verify

extract-c: extract-api extract-box extract-aead

extract-api:
	mkdir -p api-c
	$(KRML) -tmpdir api-c NaCl.fst -verbose -skip-compilation \
		$(addprefix -drop , 'Spec.\*' 'Hacl.Spec.\*' 'Hacl.Spe.\*' 'Hacl.Impl.\*' "Seq.\*" \
				    Hacl.Constants Hacl.Endianness) \
		-bundle "NaCl=NaCl,Hacl.SecretBox,Hacl.Box"

extract-box:
	mkdir -p box-c
	$(KRML) -tmpdir box-c NaCl.fst -verbose -skip-compilation \
		$(addprefix -drop , 'Spec.\*' 'Hacl.Spec.\*' 'Hacl.Spe.\*' 'Hacl.Impl.\*' "Seq.\*" \
				    Hacl.Constants Hacl.Endianness) \
		-bundle "NaCl=NaCl,Hacl.SecretBox.ZeroPad,Hacl.Box.ZeroPad"


extract-aead:
	mkdir -p aead-c
	$(KRML2) -tmpdir aead-c Chacha20Poly1305.fst -verbose \
		-drop Hacl.Bignum.Constants,Hacl.Bignum.Parameters,Hacl.Bignum.Limb,Hacl.Bignum.Wide \
		-drop Hacl.UInt16,Hacl.Types,Spec.\*,Hacl.Spec.\*,Hacl.Spe.\* \
		-drop Hacl.Constants,Hacl.Endianness,Hacl.Bignum.\*,Hacl.Spe.\*,Seq.\*,Hacl.Impl.\* \
		-drop AEAD_Poly1305_64,Chacha20 \
		-add-include '"testlib.h"' -skip-compilation -add-include '"Chacha20.h"' \
		-add-include '"AEAD_Poly1305_64.h"' -I ../salsa-family -I ../poly1305 -I ../bignum -I ../../specs

count-line:
	@echo "LOC for AEAD CHACHAPOLY"
	cloc --force-lang=ocaml Chacha20Poly1305.fst
	@echo "LOC for SECRETBOX"
	cloc --force-lang=ocaml Hacl.SecretBox.ZeroPad.fst
	@echo "LOC for BOX"
	cloc --force-lang=ocaml Hacl.Box.ZeroPad.fst

clean:
	rm -rf api-c *~ *.exe *.graph *.o *.out aead-c box-c
