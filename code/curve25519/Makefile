FSTAR_HOME?=../../../FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
HACL_HOME?=../..
include ../Makefile.include


FSTAR_LIB_FILES= \
	FStar.Mul.fst \
	FStar.Squash.fsti \
	FStar.Squash.fst \
	FStar.Classical.fst \
	FStar.StrongExcludedMiddle.fst \
	FStar.PropositionalExtensionality.fst \
	FStar.FunctionalExtensionality.fst \
	FStar.PredicateExtensionality.fst \
	FStar.List.Tot.fst \
	FStar.ListProperties.fst \
	FStar.Seq.fst \
	FStar.SeqProperties.fst \
	FStar.Math.Lib.fst \
	FStar.Math.Lemmas.fst \
	FStar.BitVector.fst \
	FStar.Int.fst \
	FStar.UInt.fst \
	FStar.UInt32.fst \
	FStar.Int32.fst \
	FStar.Int8.fst \
	FStar.Int16.fst \
	FStar.Int63.fst \
	FStar.Int64.fst \
	FStar.Int128.fst \
	FStar.UInt8.fst \
	FStar.UInt16.fst \
	FStar.UInt63.fst \
	FStar.UInt64.fst \
	FStar.UInt128.fst \
	FStar.Int.Cast.fst \
	FStar.TSet.fst \
	FStar.Set.fst \
	FStar.Map.fst \
	FStar.Heap.fst \
	FStar.Ghost.fst \
	FStar.HyperHeap.fst \
	FStar.HyperStack.fst \
	FStar.ST.fst \
	FStar.Buffer.fst

X25519_FILES= \
	Hacl.Bignum.Constants.fst \
	Hacl.Bignum.Parameters.fst \
	Hacl.Bignum.Limb.fst \
	Hacl.Bignum.Wide.fst \
	Hacl.Spec.Bignum.Field.fst \
	Hacl.Spec.Bignum.Bigint.fst \
	Hacl.Spec.Bignum.Modulo.fst \
	Hacl.Bignum.Modulo.fst \
	Hacl.Spec.Bignum.Fsum.fst \
	Hacl.Spec.Bignum.Fdifference.fst \
	Hacl.Spec.Bignum.Fscalar.fst \
	Hacl.Spec.Bignum.Fproduct.fst \
	Hacl.Spec.Bignum.Fsquare.fst \
	Hacl.Bignum.Fsum.fst \
	Hacl.Bignum.Fdifference.fst \
	Hacl.Bignum.Fscalar.fst \
	Hacl.Bignum.Fproduct.fst \
	Hacl.Bignum.Fsquare.fst \
	Hacl.Bignum.Crecip.fst \
	Hacl.Bignum.fst \
	Hacl.EC.Point.fst \
	Hacl.EC.AddAndDouble.fst \
	Hacl.EC.Format.fst \
	Hacl.EC.Ladder.fst \
	Hacl.EC.fst


POLY1305_MODULES= \
	Hacl.Bignum.Parameters \
	Hacl.Bignum.Limb \
	Hacl.Bignum.Wide \
	Hacl.Spec.Bignum.Field \
	Hacl.Spec.Bignum.Bigint \
	Hacl.Spec.Bignum.Modulo \
	Hacl.Spec.Bignum.Fsum \
	Hacl.Spec.Bignum.Fdifference \
	Hacl.Spec.Bignum.Fscalar \
	Hacl.Spec.Bignum.Fproduct \
	Hacl.Spec.Bignum.Fsquare \
	Hacl.Spec.Bignum.Crecip \
	Hacl.Bignum.Modulo \
	Hacl.Bignum.Fsum \
	Hacl.Bignum.Fdifference \
	Hacl.Bignum.Fscalar \
	Hacl.Bignum.Fproduct \
	Hacl.Bignum.Fsquare \
	Hacl.Bignum.Crecip \
	Hacl.Spec.EC.AddAndMultiply \
	Hacl.Spec.MAC.Poly1305_64 \
	Hacl.EC.Point \
	Hacl.EC.AddAndMultiply \
	Hacl.EC.Format \
	Hacl.EC.Ladder \
	Hacl.EC


verify: 
	$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack --include interfaces \
		--include ../lib --include ../bignum --include ../bignum/interfaces \
		--explicit_deps $(FSTAR_LIB_FILES) $(HACL_LIB_FILES) \
		$(X25519_FILES) \
		$(addprefix --verify_module , 	$(X25519_MODULES))


extract-c:
	mkdir -p x25519-c
	$(KREMLIN_HOME)/krml -I $(FSTAR_HOME)/ulib/hyperstack -tmpdir x25519-c -verbose \
		-I ../bignum -I ../lib/kremlin -I $(FSTAR_HOME)/../kremlin/kremlib -I $(FSTAR_HOME)/../kremlin/test \
		$(X25519_FILES) Hacl.Test.X25519.fst \
		-drop FStar -drop Hacl.Spec -drop Prims -drop Hacl.Cast -drop Hacl.UInt8 -drop Hacl.UInt32 -drop Hacl.UInt64 \
		-drop Hacl.UInt128  -drop Hacl.Bignum.Constants -drop Hacl.Bignum.Parameters -drop Hacl.Bignum.Limb -drop Hacl.Bignum.Wide \
		-bundle Hacl.Spec -bundle Hacl.Bignum -bundle Hacl.EC \
		$(FSTAR_HOME)/../kremlin/test/testlib.c -add-include '"testlib.h"' \
		-ccopt -Wno-error=pointer-sign -ccopt -Wno-error=incompatible-pointer-types \
                -ccopt -Wno-error=format= -no-prefix Hacl.Test.X25519 -ccopt -flto -ccopt -march=native -o x25519.exe
	./x25519.exe



clean:
	rm -rf *.exe *.exe.* *.out *~ x25519-c 
