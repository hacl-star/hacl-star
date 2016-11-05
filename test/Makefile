all:
	$(MAKE) allsubdirs test_box.exe

FSTAR_HOME?=/Users/bhargava/Desktop/repositories/FStar
KREMLIN_HOME=$(FSTAR_HOME)/../kremlin
HACL_HOME=..
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

test_box.exe: Hacl.Test.Box.fst
	mkdir -p box
	$(KREMLIN) $(KREMLIN_ARGS) -fsopt "--no_extract FStar.Int.Cast" \
		$(HACL_KREMLIN_FILES) $(KREMTEST)/testlib.c $^ \
		-I $(HACL_LIB) -I $(HACL_API) -I $(HACL_SYMMETRIC) -I $(HACL_EC) \
		-I $(KREMLIB) -I $(KREMTEST) -I ./bindings \
		-no-prefix Hacl.Test.Box \
		-add-include '"testlib.h"' -add-include '<sodium.h>' -no-prefix Libsodium \
		-tmpdir box -o test_box.exe -ldopt "-lsodium" # -ccopt "-m32"
	./test_box.exe

test_tube.exe: tube/PaddedFileIO.c tube/SocketIO.c tube/Hacl.Tube.fst
	mkdir -p box
	$(KREMLIN) $(KREMLIN_ARGS) -fsopt "--no_extract FStar.Int.Cast" \
		$(HACL_KREMLIN_FILES) $(KREMTEST)/testlib.c $^ \
		-I $(HACL_LIB) -I $(HACL_API) -I $(HACL_SYMMETRIC) -I $(HACL_EC) \
		-I $(KREMLIB) -I $(KREMTEST) -I ./bindings -I ./tube \
		-no-prefix Hacl.Tube \
		-add-include '"testlib.h"' -add-include '<sodium.h>' -no-prefix Libsodium \
		-tmpdir box -o test_tube.exe -ldopt "-lsodium" # -ccopt "-m32"
	./test_box.exe

tube-c.exe: c/tube.c
	mkdir -p tmp 
	$(KREMLIN) $(KREMLIN_ARGS) -fsopt "--no_extract FStar.Int.Cast" \
		$(HACL_KREMLIN_FILES) $(HACL_API)/Hacl.Box.fst $(KREMTEST)/testlib.c c/FStar_FileIO.c c/FStar_SocketIO.c c/tube.c \
		-I $(HACL_LIB) -I $(HACL_API) -I $(HACL_SYMMETRIC) -I $(HACL_EC) \
		-I $(KREMLIB) -I $(KREMTEST) -I ./c \
		-tmpdir tmp -o tube-c.exe -ldopt "-lsodium" # -ccopt "-m32"


tube-star.exe: tube/Box.Ideal.fst tube/PaddedFileIO_impl.c tube/SocketIO_impl.c tube/Hacl.Tube.fst tube/tube.c
	mkdir -p tmp 
	$(KREMLIN) $(KREMLIN_ARGS) -fsopt "--no_extract FStar.Int.Cast" \
		$(HACL_KREMLIN_FILES) $(KREMTEST)/testlib.c $^ \
		-I $(HACL_LIB) -I $(HACL_API) -I $(HACL_SYMMETRIC) -I $(HACL_EC) \
		-I $(KREMLIB) -I $(KREMTEST) -I ./c -I ./bindings -I ./tube -no-prefix Libsodium \
		-add-include '<sodium.h>' -add-include '"testlib.h"' \
		-tmpdir tmp -o tube-star.exe -ldopt "-lsodium"
	cp text.txt tmp/bla.txt

tube-toy.exe: $(HACL_API)/Hacl.Constants.fst tube/Hacl.Tube.fst
	mkdir -p tmp 
	$(KREMLIN) $(KREMLIN_ARGS) $(HACL_KREMLIN_FILES) $(KREMTEST)/testlib.c $^ \
		-I $(HACL_LIB) -I $(HACL_API)/api -I $(HACL_SYMMETRIC) -I $(HACL_EC) \
		-I $(KREMLIB) -I $(KREMTEST) -I ./c -I ./bindings -I ./tube \
		-tmpdir tmp -skip-compilation

receive	:
	rm -f bla.txt
	./tube-star.exe receive 5001 -k dfcf8b782a2a72f65ee24f85fa68ab1a10b3b555751283c5f0bcdb20e1a6e4a8 -p 4d187de7a95fe760ba7ffc9a1ba4229eea9cd1136fe609bdc58816e3cf4d3350

send:
	cd tmp && ../tube-star.exe send bla.txt localhost:5001 -k 4d922658eb6d4aef64a83644a18e60e61a57c245aa8e5e9a93926cb2b317ffd7 -p 223fc224f2c9906fd4bbb1313236ecc4f36ed2f7e95b5fb1deafc459b19ab069

perf1: test_api.exe
	./test_api.exe perf1

perf2: test_api.exe
	./test_api.exe perf2

perf3: test_api.exe
	./test_api.exe perf3

tweetnacl: $(KREMTEST)/testlib.c c/randombytes.c c/tweetnacl.c c/tweetnacl_test.c
	gcc-5 -Wno-unused-but-set-variable -std=c11 -Wall -Werror -Wno-parentheses -Wno-unused-variable -g -O3 -fwrapv -I $(KREMTEST) -I c $^ -o tweetnacl_test.exe
	./tweetnacl_test.exe

blah:
	gcc-6 -O3 -march=native -Wall -Werror -Wno-parentheses -Wno-unused-variable -fwrapv -I FSTAR_HOME/ulib/hyperstack -I ../lib/hyperstack -I ../crypto -I ../crypto/symmetric -I ../crypto/ec -I ../../kremlin/kremlib -I ../../kremlin/test -I /Users/bhargava/Desktop/repositories/kremlin/kremlib -I tmp -Wno-error=pointer-sign \
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
		/Users/bhargava/Desktop/repositories/kremlin/kremlib/kremlib.c \
		c/test_api.c \
		../../kremlin/test/testlib.c \
		-o test_api.exe -lsodium


test32bits:
	gcc-6 -m32 -Wall -Werror -Wno-parentheses -Wno-unused-variable -g -O3 -fwrapv -I FSTAR_HOME/ulib/hyperstack -I ../lib/hyperstack -I ../crypto -I ../crypto/symmetric -I ../crypto/ec -I ../../kremlin/kremlib -I ../../kremlin/test -I /Users/bhargava/Desktop/repositories/kremlin/kremlib -I tmp -Wno-error=pointer-sign \
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
		/Users/bhargava/Desktop/repositories/kremlin/kremlib/kremlib.c \
		../../kremlin/test/testlib.c \
		-c



gprof:
	gcc-6 -Wall -Werror -Wno-parentheses -Wno-unused-variable -g -O3 -fwrapv -I FSTAR_HOME/ulib/hyperstack -I ../lib/hyperstack -I ../crypto -I ../crypto/symmetric -I ../crypto/ec -I ../../kremlin/kremlib -I ../../kremlin/test -I /Users/bhargava/Desktop/repositories/kremlin/kremlib -I tmp -Wno-error=pointer-sign \
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
		/Users/bhargava/Desktop/repositories/kremlin/kremlib/kremlib.c \
		c/test_api.c \
		../../kremlin/test/testlib.c \
		-o test_api.exe -lsodium -pg

clean:
	rm -rf *~ *.exe *.out *.o *.c *.h *.cmi *.cmo *.cmx *.krml ./tmp ./box
	$(MAKE) -C symmetric clean
	$(MAKE) -C ec clean
# 	$(MAKE) -C hash clean
# 	$(MAKE) -C hmac clean
# 	$(MAKE) -C hkdf clean
