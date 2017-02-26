FSTAR_HOME?=../../../dependencies/FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
HACL_HOME?=../..
include ../Makefile.include

API_FILES= \
	Hacl.Constants.fst \
	Hacl.SecretBox.fst \
	Hacl.Box.fst

FSTARB=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib/kremlin --include ../salsa-family/interfaces --incude ../curve25519/interfaces \
		--include ../poly1305/interfaces


FSTAR_CT=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib/ --include ../salsa-family/interfaces --incude ../curve25519/interfaces \
		--include ../poly1305/interfaces


KRML=$(KREMLIN_HOME)/krml -I ../lib/kremlin -I ../salsa-family/interfaces -I ../curve25519/interfaces \
		-I ../poly1305/interfaces -I ../../specs \
		-drop FStar -drop Hacl.Spec -drop Prims -drop Hacl.Cast -drop Hacl.UInt8 \
		-drop Hacl.UInt32 -drop Hacl.UInt64 -drop Hacl.UInt128 \

# Lax typechecking against the restricted integer interface
%.fst-ct: %.fst
	$(FSTAR_CT) --lax $^

all-ct: $(addsuffix -ct, $(API_FILES))

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

extract-c:
	mkdir -p api-c
	$(KRML) -tmpdir api-c ../salsa-family/Hacl.Symmetric.HSalsa20.fst NaCl.fst -verbose \
		-drop Hacl.Bignum.Constants -drop Hacl.Bignum.Parameters -drop Hacl.Bignum.Limb -drop Hacl.Bignum.Wide \
		-drop Hacl.UInt16 -drop Hacl.Types -drop 'Spec.\*' -drop 'Hacl.Spec.\*' \
		-drop Hacl.Constants -drop "Hacl.Endianness" \
		-bundle "NaCl=NaCl,Hacl.SecretBox,Hacl.Box" \
		-add-include '"testlib.h"' -skip-compilation -add-include '"Salsa20.h"' \
		-add-include '"Poly1305_64.h"' -add-include '"Curve25519.h"' 
extract-aead:
	mkdir -p aead-c
	$(KRML) -tmpdir aead-c Hacl.AEAD.Chacha20Poly1305.fst -verbose \
		-drop Hacl.Bignum.Constants -drop Hacl.Bignum.Parameters -drop Hacl.Bignum.Limb -drop Hacl.Bignum.Wide \
		-drop Hacl.UInt16 -drop Hacl.Types -drop 'Spec.\*' -drop 'Hacl.Spec.\*' \
		-drop Hacl.Constants -drop "Hacl.Endianness" -drop 'Combinators' \
		-add-include '"testlib.h"' -skip-compilation -add-include '"Chacha20.h"' \
		-add-include '"Poly1305_64.h"' -I ../salsa-family -I ../poly1305 -I ../bignum -I ../../specs -I ../../specs/generic -I ../../specs/experimental

clean:
	rm -rf api-c *~ *.exe *.graph *.o *.out
