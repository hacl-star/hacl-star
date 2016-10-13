all:
	make clean
	$(MAKE) -C symmetric
	$(MAKE) -C ec
#	$(MAKE) -C hash
#	$(MAKE) -C hmac
#	$(MAKE) -C hkdf

FSTAR_HOME?=../../FStar
FSTAR=$(FSTAR_HOME)/bin/fstar.exe
FSTAR_ARGS=

HACL_HOME?=..
HACL_LIB=$(HACL_HOME)/lib/hst
HACL_KREMLIN=$(HACL_LIB)/kremlin
HACL_KREMLIN_FILES=$(addprefix $(HACL_KREMLIN)/, Hacl.UInt8.fst Hacl.UInt16.fst Hacl.UInt32.fst Hacl.UInt64.fst Hacl.UInt128.fst Hacl.Cast.fst Hacl.Policies.fst)
HACL_API=$(HACL_HOME)/crypto_hst
HACL_SYMMETRIC=$(HACL_API)/symmetric
HACL_EC=$(HACL_API)/ec

KREMLIN_HOME?=../../kremlin
KREMLIN=$(KREMLIN_HOME)/krml
KREMLIN_ARGS=-verbose
KREMLIB=$(KREMLIN_HOME)/kremlib
KREMTEST=$(KREMLIN_HOME)/test

kremlin:
	$(MAKE) -C symmetric chacha-kremlin poly-kremlin aead-kremlin
	$(MAKE) api-kremlin

lax:
	$(FSTAR) --lax $(HACL_API)/Hacl.Box.fst --include $(HACL_LIB) --include $(HACL_SYMMETRIC) --include $(HACL_EC) --include $(HACL_API)

api-kremlin:
	mkdir -p tmp
	$(KREMLIN) $(KREMLIN_ARGS) \
		$(HACL_KREMLIN_FILES) $(HACL_API)/Hacl.Box.fst $(KREMTEST)/testlib.c c/test_api.c \
		-I $(HACL_LIB) -I $(HACL_API) -I $(HACL_SYMMETRIC) -I $(HACL_EC) \
		-I $(KREMLIB) -I $(KREMTEST) \
		-tmpdir tmp -o test_api.exe -ldopt "-lsodium"
	./test_api.exe

# test:
# 	gcc-5 -std=c11 -Wall -Werror -Wno-parentheses -Wno-unused-variable -Wno-unused-but-set-variable -g -O3 -fwrapv -I ../lib/hst -I ../crypto_hst -I ../crypto_hst/symmetric -I ../crypto_hst/ec -I ../../kremlin/kremlib -I ../../kremlin/test -I /home/jkz/dev/kremlin/kremlib -I tmp -c c/test_api.c -o tmp/test_api.o
# 	gcc-5 -std=c11 -Wall -Werror -Wno-parentheses -Wno-unused-variable -Wno-unused-but-set-variable -g -O3 -fwrapv -I ../lib/hst -I ../crypto_hst -I ../crypto_hst/symmetric -I ../crypto_hst/ec -I ../../kremlin/kremlib -I ../../kremlin/test -I /home/jkz/dev/kremlin/kremlib -I tmp tmp/FStar_Mul.o tmp/FStar_List_Tot.o tmp/FStar_ListProperties.o tmp/FStar_Seq.o tmp/FStar_Math_Lib.o tmp/FStar_Math_Lemmas.o tmp/FStar_UInt.o tmp/FStar_FunctionalExtensionality.o tmp/FStar_PropositionalExtensionality.o tmp/FStar_PredicateExtensionality.o tmp/FStar_TSet.o tmp/FStar_Set.o tmp/FStar_Map.o tmp/FStar_Heap.o tmp/FStar_ST.o tmp/FStar_All.o tmp/Hacl_UInt64.o tmp/Hacl_UInt128.o tmp/Hacl_UInt32.o tmp/Hacl_UInt8.o tmp/FStar_Int.o tmp/FStar_Int_Cast.o tmp/Hacl_Cast.o tmp/FStar_HyperHeap.o tmp/FStar_Squash.o tmp/FStar_Classical.o tmp/FStar_SeqProperties.o tmp/FStar_Ghost.o tmp/FStar_Buffer.o tmp/FStar_Buffer_Quantifiers.o tmp/Hacl_EC_Curve25519_Parameters.o tmp/Hacl_EC_Curve25519_Bigint.o tmp/Hacl_EC_Curve25519_Bignum_FsumWide.o tmp/Hacl_EC_Curve25519_Bignum_Fscalar.o tmp/Hacl_EC_Curve25519_Bignum_Fproduct.o tmp/Hacl_EC_Curve25519_Bignum_Fdifference.o tmp/Hacl_EC_Curve25519_Bignum_Fsum.o tmp/Hacl_EC_Curve25519_Bignum_Modulo.o tmp/Hacl_EC_Curve25519_Bignum.o tmp/Hacl_EC_Curve25519_PPoint.o tmp/Hacl_EC_Curve25519_AddAndDouble.o tmp/Utils.o tmp/Hacl_Types.o tmp/Hacl_Symmetric_Poly1305_Parameters.o tmp/Hacl_Symmetric_Poly1305_Bigint.o tmp/Hacl_SBuffer.o tmp/Hacl_Symmetric_Poly1305_Bignum_Lemmas.o tmp/Hacl_Symmetric_Poly1305_Bignum.o tmp/Hacl_Symmetric_Poly1305_Lemmas.o tmp/Hacl_Symmetric_Poly1305.o tmp/Hacl_Symmetric_Salsa20.o tmp/Hacl_Symmetric_XSalsa20.o tmp/Hacl_Policies.o tmp/Hacl_Constants.o tmp/Hacl_SecretBox.o tmp/Hacl_EC_Curve25519_Ladder.o tmp/Hacl_EC_Curve25519_Crecip.o tmp/Hacl_EC_Curve25519.o tmp/Hacl_Box.o tmp/kremlib.o tmp/test_api.o tmp/testlib.o -o test_api.exe -lsodium
# 	./test_api.exe

clean:
	rm -rf *~ *.exe *.out *.o *.c *.h *.cmi *.cmo *.cmx *.krml ./tmp
	$(MAKE) -C symmetric clean
	$(MAKE) -C ec clean
	$(MAKE) -C hash clean
	$(MAKE) -C hmac clean
	$(MAKE) -C hkdf clean
