FSTAR_HOME?=../../../../../FStar
KREMLIN_HOME=$(FSTAR_HOME)/../kremlin
ARTIFACT_HOME=../..
include ../../Makefile.include

MODULES=Hacl.Symmetric.Poly1305_64.Parameters \
	Hacl.Symmetric.Poly1305_64.Bigint \
	Hacl.Symmetric.Poly1305_64 \
	Hacl.EC.Curve25519.Parameters \
	Hacl.EC.Curve25519.Bigint \
	Hacl.EC.Curve25519.Utils \
	Hacl.EC.Curve25519.Bignum.Fdifference \
	Hacl.EC.Curve25519.Bignum.Fproduct \
	Hacl.EC.Curve25519.Bignum.Fscalar \
	Hacl.EC.Curve25519.Bignum.Fsum \
	Hacl.EC.Curve25519.Bignum.Modulo \
	Hacl.EC.Curve25519.Bignum \
	Hacl.EC.Curve25519.Crecip \
	Hacl.EC.Curve25519.PPoint \
	Hacl.EC.Curve25519.AddAndDouble \
	Hacl.EC.Curve25519.Ladder \
	Hacl.EC.Curve25519 \
	Hacl.Symmetric.HSalsa20 \
	Hacl.Symmetric.XSalsa20 \
	Hacl.SecretBox \
	Hacl.Box

INCLUDES=


%.fst-ver-ct: %.fst
	$(FSTAR) $(FSTAR_OPTIONS_VER) $(INCLUDES) --verify_module $(basename $(notdir $@)) $^ --include $(LIB)

ver: $(addsuffix .fst-ver-ct, $(MODULES))

test: Hacl.Test.fst
	$(KREMLIN) $(KREMLIN_ARGS) $^ -no-prefix Hacl.Test -add-include '"testlib.h"' \
		$(KREMTEST)/testlib.c -I $(LIB_KRML) -I $(KREMLIB) -I $(KREMTEST) \
		-tmpdir tmp -o test_crypto.exe
	./test_crypto.exe

extract: Hacl.Symmetric.XSalsa20.fst Hacl.Box.fst
	$(KREMLIN) $(KREMLIN_ARGS) $^ -I $(LIB_KRML) -tmpdir extracted_code -skip-compilation


CFILES=Prims.c FStar_Mul.c FStar_Squash.c FStar_StrongExcludedMiddle.c FStar_List_Tot.c FStar_Classical.c FStar_ListProperties.c FStar_SeqProperties.c FStar_Math_Lemmas.c FStar_BitVector.c FStar_UInt.c FStar_Int.c FStar_FunctionalExtensionality.c FStar_PropositionalExtensionality.c FStar_PredicateExtensionality.c FStar_TSet.c FStar_Set.c FStar_Map.c FStar_Ghost.c FStar_All.c Hacl_UInt64.c Hacl_UInt128.c Hacl_UInt32.c Hacl_UInt8.c Hacl_Cast.c FStar_Buffer.c FStar_Buffer_Quantifiers.c Hacl_EC_Curve25519_Parameters.c Hacl_EC_Curve25519_Bigint.c Hacl_EC_Curve25519_Utils.c Hacl_EC_Curve25519_Bignum_Fproduct.c Hacl_EC_Curve25519_Bignum_Fscalar.c Hacl_EC_Curve25519_Bignum_Fdifference.c Hacl_EC_Curve25519_Bignum_Fsum.c Hacl_EC_Curve25519_Bignum_Modulo.c Hacl_EC_Curve25519_Bignum.c Hacl_EC_Curve25519_PPoint.c Hacl_EC_Curve25519_AddAndDouble.c Hacl_Types.c Hacl_Symmetric_Poly1305_64_Parameters.c Hacl_Symmetric_Poly1305_64_Bigint.c Hacl_Symmetric_HSalsa20.c Hacl_Symmetric_Poly1305_64.c Hacl_Symmetric_Salsa20.c Hacl_Policies.c Hacl_Constants.c Hacl_SecretBox.c Hacl_EC_Curve25519_Ladder.c Hacl_EC_Curve25519_Crecip.c Hacl_EC_Curve25519.c Hacl_Box.c Hacl_Symmetric_XSalsa20.c

bench.exe: $(addprefix extracted_code/, $(CFILES)) bench.c
	gcc -O3 $(addprefix extracted_code/, $(CFILES)) -I $(KREMLIB) -I $(KREMTEST) \
		-I extracted_code $(KREMLIB)/kremlib.c $(KREMTEST)/testlib.c bench.c -o bench.exe

bench: bench.exe
	./bench.exe box
	./bench.exe poly1305
	./bench.exe xsalsa20
	./bench.exe curve25519

clean:
	rm -rf tmp
	rm -f *~ *.exe
