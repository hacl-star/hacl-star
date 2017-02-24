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

KRML=$(KREMLIN_HOME)/krml -I ../lib/kremlin -I ../salsa-family/interfaces -I ../curve25519/interfaces \
		-I ../poly1305/interfaces -I ../../specs \
		-drop FStar -drop Hacl.Spec -drop Prims -drop Hacl.Cast -drop Hacl.UInt8 \
		-drop Hacl.UInt32 -drop Hacl.UInt64 -drop Hacl.UInt128 \


%.fst-verify: %.fst
	$(FSTARB) $^ --use_hints

verify: $(addsuffix -verify, $(API_FILES))

extract-c:
	mkdir -p api-c
	$(KRML) -tmpdir api-c ../salsa-family/Hacl.Symmetric.HSalsa20.fst NaCl.fst -verbose \
		-drop Hacl.Bignum.Constants -drop Hacl.Bignum.Parameters -drop Hacl.Bignum.Limb -drop Hacl.Bignum.Wide \
		-drop Hacl.UInt16 -drop Hacl.Types -drop 'Spec.\*' -drop 'Hacl.Spec.\*' \
		-drop Hacl.Constants -drop "Hacl.Endianness" \
		-bundle "NaCl=NaCl,Hacl.SecretBox,Hacl.Box" \
		-add-include '"testlib.h"' -skip-compilation -add-include '"Salsa20.h"' \
		-add-include '"Poly1305_64.h"' -add-include '"Curve25519.h"' 

clean:
	rm -rf api-c *~ *.exe *.graph *.o *.out

# extract-c:
# 	mkdir -p api-c
# 	$(KREMLIN_HOME)/krml -I $(FSTAR_HOME)/ulib/hyperstack -tmpdir api-c -verbose \
# 		-I ../bignum -I ../lib/kremlin -I $(FSTAR_HOME)/../kremlin/kremlib -I $(FSTAR_HOME)/../kremlin/test \
# 		-I ../salsa-family -I ../poly1305 -I ../curve25519 $(API_FILES) \
# 		-I ../../specs \
# 		-drop FStar -drop Hacl.Spec -drop Prims -drop Hacl.Cast -drop Hacl.UInt8 -drop Hacl.UInt32 -drop Hacl.UInt64 \
# 		-drop Hacl.UInt128  -drop Hacl.Bignum.Constants -drop Hacl.Bignum.Parameters -drop Hacl.Bignum.Limb -drop Hacl.Bignum.Wide \
# 		-bundle "Poly1305_64=Poly1305_64,Hacl.Bignum.\*,Hacl.Spec.\*" \
# 		-bundle "Curve25510=Curve25519,Hacl.Bignum.\*,Hacl.Spec.\*" \
# 		$(FSTAR_HOME)/../kremlin/kremlib/testlib.c -add-include '"testlib.h"' -skip-compilation
