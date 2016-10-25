all:
	make clean
	$(MAKE) allsubdirs test_api.exe

FSTAR_HOME?=/Users/bhargava/Desktop/repositories/FStar
KREMLIN_HOME=$(FSTAR_HOME)/../kremlin
HACL_HOME?=..
include $(HACL_HOME)/lib/hyperstack/Makefile.include
SUBDIRS=symmetric ec # hash hmac hkdf
allsubdirs: $(addsuffix .all , $(SUBDIRS))

%.all:
	$(MAKE) -C $(basename $@)

test_api.exe: c/test_api.c
	mkdir -p tmp 
	$(KREMLIN) $(KREMLIN_ARGS) -fsopt "--no_extract FStar.Int.Cast" \
		$(HACL_KREMLIN_FILES) $(HACL_API)/Hacl.Box.fst $(KREMTEST)/testlib.c c/FStar_FileIO.c c/FStar_SocketIO.c c/test_api.c \
		-I $(HACL_LIB) -I $(HACL_API) -I $(HACL_SYMMETRIC) -I $(HACL_EC) \
		-I $(KREMLIB) -I $(KREMTEST) \
		-tmpdir tmp -o test_api.exe -ldopt "-lsodium" # -ccopt "-m32"
	./test_api.exe

tube.exe: c/tube.c
	mkdir -p tmp 
	$(KREMLIN) $(KREMLIN_ARGS) -fsopt "--no_extract FStar.Int.Cast" \
		$(HACL_KREMLIN_FILES) $(HACL_API)/Hacl.Box.fst $(KREMTEST)/testlib.c c/FStar_FileIO.c c/FStar_SocketIO.c c/tube.c \
		-I $(HACL_LIB) -I $(HACL_API) -I $(HACL_SYMMETRIC) -I $(HACL_EC) \
		-I $(KREMLIB) -I $(KREMTEST) -I ./c \
		-tmpdir tmp -o tube.exe -ldopt "-lsodium" # -ccopt "-m32"

perf1: test_api.exe
	./test_api.exe perf1

perf2: test_api.exe
	./test_api.exe perf2

perf3: test_api.exe
	./test_api.exe perf3

blah:
	gcc-5 -m32 -Wall -Werror -Wno-parentheses -Wno-unused-variable -g -O3 -fwrapv -I FSTAR_HOME/ulib/hyperstack -I ../lib/hyperstack -I ../crypto -I ../crypto/symmetric -I ../crypto/ec -I ../../kremlin/kremlib -I ../../kremlin/test -I /home/jkz/dev/kremlin/kremlib -I tmp -Wno-error=pointer-sign \
		tmp/FStar_Mul.c \
		tmp/FStar_List_Tot.c \
		tmp/FStar_ListProperties.c \
		tmp/FStar_Seq.c \
		tmp/FStar_Math_Lib.c \
		tmp/FStar_Math_Lemmas.c \
		tmp/FStar_BitVector.c \
		tmp/FStar_UInt.c \
		tmp/FStar_Int.c \
		tmp/FStar_FunctionalExtensionality.c \
		tmp/FStar_PropositionalExtensionality.c \
		tmp/FStar_PredicateExtensionality.c \
		tmp/FStar_TSet.c \
		tmp/FStar_Set.c \
		tmp/FStar_Map.c \
		tmp/FStar_Heap.c \
		tmp/FStar_HyperHeap.c \
		tmp/FStar_Ghost.c \
		tmp/FStar_ST.c \
		tmp/FStar_All.c \
		tmp/Hacl_UInt64.c \
		tmp/Hacl_UInt128.c \
		tmp/Hacl_UInt32.c \
		tmp/Hacl_UInt8.c \
		tmp/Hacl_Cast.c \
		tmp/FStar_Squash.c \
		tmp/FStar_Classical.c \
		tmp/FStar_SeqProperties.c \
		tmp/FStar_Buffer.c \
		tmp/FStar_Buffer_Quantifiers.c \
		tmp/Hacl_EC_Curve25519_Parameters.c \
		tmp/Hacl_EC_Curve25519_Bigint.c \
		tmp/Hacl_EC_Curve25519_Bignum_FsumWide.c \
		tmp/Hacl_EC_Curve25519_Bignum_Fscalar.c \
		tmp/Hacl_EC_Curve25519_Bignum_Fproduct.c \
		tmp/Hacl_EC_Curve25519_Bignum_Fdifference.c \
		tmp/Hacl_EC_Curve25519_Bignum_Fsum.c \
		tmp/Hacl_EC_Curve25519_Bignum_Modulo.c \
		tmp/Hacl_EC_Curve25519_Bignum.c \
		tmp/Hacl_EC_Curve25519_PPoint.c \
		tmp/Hacl_EC_Curve25519_AddAndDouble.c \
		tmp/Utils.c \
		tmp/Hacl_Types.c \
		tmp/Hacl_Symmetric_Poly1305_64_Parameters.c \
		tmp/Hacl_Symmetric_Poly1305_64_Bigint.c \
		tmp/Hacl_Symmetric_HSalsa20.c \
		tmp/Hacl_Symmetric_Poly1305_Parameters.c \
		tmp/Hacl_Symmetric_Poly1305_64.c \
		tmp/Hacl_Symmetric_Poly1305_Spec.c \
		tmp/Hacl_Symmetric_Poly1305_Bigint.c \
		tmp/Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1.c \
		tmp/Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part2.c \
		tmp/Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part3.c \
		tmp/Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part4.c \
		tmp/Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part5.c \
		tmp/Hacl_Symmetric_Poly1305_Bignum.c \
		tmp/Hacl_Symmetric_Poly1305.c \
		tmp/Hacl_Symmetric_Salsa20.c \
		tmp/Hacl_Symmetric_XSalsa20.c \
		tmp/Hacl_Policies.c \
		tmp/Hacl_Constants.c \
		tmp/Hacl_SecretBox.c \
		tmp/Hacl_EC_Curve25519_Ladder.c \
		tmp/Hacl_EC_Curve25519_Crecip.c \
		tmp/Hacl_EC_Curve25519.c \
		tmp/Hacl_Box.c \
		/home/jkz/dev/kremlin/kremlib/kremlib.c \
		c/test_api.c \
		../../kremlin/test/testlib.c \
		-o test_api.exe -lsodium


test32bits:
	gcc-5 -m32 -Wall -Werror -Wno-parentheses -Wno-unused-variable -g -O3 -fwrapv -I FSTAR_HOME/ulib/hyperstack -I ../lib/hyperstack -I ../crypto -I ../crypto/symmetric -I ../crypto/ec -I ../../kremlin/kremlib -I ../../kremlin/test -I /home/jkz/dev/kremlin/kremlib -I tmp -Wno-error=pointer-sign \
		tmp/FStar_Mul.c \
		tmp/FStar_List_Tot.c \
		tmp/FStar_ListProperties.c \
		tmp/FStar_Seq.c \
		tmp/FStar_Math_Lib.c \
		tmp/FStar_Math_Lemmas.c \
		tmp/FStar_BitVector.c \
		tmp/FStar_UInt.c \
		tmp/FStar_Int.c \
		tmp/FStar_FunctionalExtensionality.c \
		tmp/FStar_PropositionalExtensionality.c \
		tmp/FStar_PredicateExtensionality.c \
		tmp/FStar_TSet.c \
		tmp/FStar_Set.c \
		tmp/FStar_Map.c \
		tmp/FStar_Heap.c \
		tmp/FStar_HyperHeap.c \
		tmp/FStar_Ghost.c \
		tmp/FStar_ST.c \
		tmp/FStar_All.c \
		tmp/Hacl_UInt64.c \
		tmp/Hacl_UInt128.c \
		tmp/Hacl_UInt32.c \
		tmp/Hacl_UInt8.c \
		tmp/Hacl_Cast.c \
		tmp/FStar_Squash.c \
		tmp/FStar_Classical.c \
		tmp/FStar_SeqProperties.c \
		tmp/FStar_Buffer.c \
		tmp/FStar_Buffer_Quantifiers.c \
		tmp/Hacl_EC_Curve25519_Parameters.c \
		tmp/Hacl_EC_Curve25519_Bigint.c \
		tmp/Hacl_EC_Curve25519_Bignum_FsumWide.c \
		tmp/Hacl_EC_Curve25519_Bignum_Fscalar.c \
		tmp/Hacl_EC_Curve25519_Bignum_Fproduct.c \
		tmp/Hacl_EC_Curve25519_Bignum_Fdifference.c \
		tmp/Hacl_EC_Curve25519_Bignum_Fsum.c \
		tmp/Hacl_EC_Curve25519_Bignum_Modulo.c \
		tmp/Hacl_EC_Curve25519_Bignum.c \
		tmp/Hacl_EC_Curve25519_PPoint.c \
		tmp/Hacl_EC_Curve25519_AddAndDouble.c \
		tmp/Utils.c \
		tmp/Hacl_Types.c \
		tmp/Hacl_Symmetric_Poly1305_64_Parameters.c \
		tmp/Hacl_Symmetric_Poly1305_64_Bigint.c \
		tmp/Hacl_Symmetric_HSalsa20.c \
		tmp/Hacl_Symmetric_Poly1305_Parameters.c \
		tmp/Hacl_Symmetric_Poly1305_64.c \
		tmp/Hacl_Symmetric_Poly1305_Spec.c \
		tmp/Hacl_Symmetric_Poly1305_Bigint.c \
		tmp/Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1.c \
		tmp/Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part2.c \
		tmp/Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part3.c \
		tmp/Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part4.c \
		tmp/Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part5.c \
		tmp/Hacl_Symmetric_Poly1305_Bignum.c \
		tmp/Hacl_Symmetric_Poly1305.c \
		tmp/Hacl_Symmetric_Salsa20.c \
		tmp/Hacl_Symmetric_XSalsa20.c \
		tmp/Hacl_Policies.c \
		tmp/Hacl_Constants.c \
		tmp/Hacl_SecretBox.c \
		tmp/Hacl_EC_Curve25519_Ladder.c \
		tmp/Hacl_EC_Curve25519_Crecip.c \
		tmp/Hacl_EC_Curve25519.c \
		tmp/Hacl_Box.c \
		/home/jkz/dev/kremlin/kremlib/kremlib.c \
		../../kremlin/test/testlib.c \
		-c



gprof:
	gcc-5 -Wall -Werror -Wno-parentheses -Wno-unused-variable -g -O3 -fwrapv -I FSTAR_HOME/ulib/hyperstack -I ../lib/hyperstack -I ../crypto -I ../crypto/symmetric -I ../crypto/ec -I ../../kremlin/kremlib -I ../../kremlin/test -I /home/jkz/dev/kremlin/kremlib -I tmp -Wno-error=pointer-sign \
		tmp/FStar_Mul.c \
		tmp/FStar_List_Tot.c \
		tmp/FStar_ListProperties.c \
		tmp/FStar_Seq.c \
		tmp/FStar_Math_Lib.c \
		tmp/FStar_Math_Lemmas.c \
		tmp/FStar_BitVector.c \
		tmp/FStar_UInt.c \
		tmp/FStar_Int.c \
		tmp/FStar_FunctionalExtensionality.c \
		tmp/FStar_PropositionalExtensionality.c \
		tmp/FStar_PredicateExtensionality.c \
		tmp/FStar_TSet.c \
		tmp/FStar_Set.c \
		tmp/FStar_Map.c \
		tmp/FStar_Heap.c \
		tmp/FStar_HyperHeap.c \
		tmp/FStar_Ghost.c \
		tmp/FStar_ST.c \
		tmp/FStar_All.c \
		tmp/Hacl_UInt64.c \
		tmp/Hacl_UInt128.c \
		tmp/Hacl_UInt32.c \
		tmp/Hacl_UInt8.c \
		tmp/FStar_Int_Cast.c \
		tmp/Hacl_Cast.c \
		tmp/FStar_Squash.c \
		tmp/FStar_Classical.c \
		tmp/FStar_SeqProperties.c \
		tmp/FStar_Buffer.c \
		tmp/FStar_Buffer_Quantifiers.c \
		tmp/Hacl_EC_Curve25519_Parameters.c \
		tmp/Hacl_EC_Curve25519_Bigint.c \
		tmp/Hacl_EC_Curve25519_Bignum_FsumWide.c \
		tmp/Hacl_EC_Curve25519_Bignum_Fscalar.c \
		tmp/Hacl_EC_Curve25519_Bignum_Fproduct.c \
		tmp/Hacl_EC_Curve25519_Bignum_Fdifference.c \
		tmp/Hacl_EC_Curve25519_Bignum_Fsum.c \
		tmp/Hacl_EC_Curve25519_Bignum_Modulo.c \
		tmp/Hacl_EC_Curve25519_Bignum.c \
		tmp/Hacl_EC_Curve25519_PPoint.c \
		tmp/Hacl_EC_Curve25519_AddAndDouble.c \
		tmp/Utils.c \
		tmp/Hacl_Types.c \
		tmp/Hacl_Symmetric_Poly1305_64_Parameters.c \
		tmp/Hacl_Symmetric_Poly1305_64_Bigint.c \
		tmp/Hacl_Symmetric_HSalsa20.c \
		tmp/Hacl_Symmetric_Poly1305_Parameters.c \
		tmp/Hacl_Symmetric_Poly1305_64.c \
		tmp/Hacl_Symmetric_Poly1305_Spec.c \
		tmp/Hacl_Symmetric_Poly1305_Bigint.c \
		tmp/Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1.c \
		tmp/Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part2.c \
		tmp/Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part3.c \
		tmp/Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part4.c \
		tmp/Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part5.c \
		tmp/Hacl_Symmetric_Poly1305_Bignum.c \
		tmp/Hacl_Symmetric_Poly1305.c \
		tmp/Hacl_Symmetric_Salsa20.c \
		tmp/Hacl_Symmetric_XSalsa20.c \
		tmp/Hacl_Policies.c \
		tmp/Hacl_Constants.c \
		tmp/Hacl_SecretBox.c \
		tmp/Hacl_EC_Curve25519_Ladder.c \
		tmp/Hacl_EC_Curve25519_Crecip.c \
		tmp/Hacl_EC_Curve25519.c \
		tmp/Hacl_Box.c \
		/home/jkz/dev/kremlin/kremlib/kremlib.c \
		c/test_api.c \
		../../kremlin/test/testlib.c \
		-o test_api.exe -lsodium -pg

clean:
	rm -rf *~ *.exe *.out *.o *.c *.h *.cmi *.cmo *.cmx *.krml ./tmp
	$(MAKE) -C symmetric clean
	$(MAKE) -C ec clean
# 	$(MAKE) -C hash clean
# 	$(MAKE) -C hmac clean
# 	$(MAKE) -C hkdf clean
