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

POLY1305_FILES= \
	Hacl.Bignum.Constants.fst \
	Hacl.Bignum.Parameters.fst \
	Hacl.Bignum.Limb.fst \
	Hacl.Bignum.Wide.fst \
	Hacl.Spec.Bignum.Field.fst \
	Hacl.Spec.Bignum.Bigint.fst \
	Hacl.Spec.Bignum.Modulo.fst \
	Hacl.Bignum.Modulo.fst \
	Hacl.Spec.Bignum.Fsum.fst \
	Hacl.Spec.Bignum.Fproduct.fst \
	Hacl.Bignum.Fsum.fst \
	Hacl.Bignum.Fproduct.fst \
	Hacl.Spec.Bignum.AddAndMultiply.fst \
	Hacl.Spec.MAC.Poly1305_64.fst \
	Hacl.MAC.Poly1305_64.fst

POLY1305_SPECIFIC= \
	Hacl.Bignum.Constants.fst \
	Hacl.Bignum.Parameters.fst \
	Hacl.Spec.Bignum.Modulo.fst \
	Hacl.Bignum.Modulo.fst \
	Hacl.Spec.Bignum.AddAndMultiply.fst \
	Hacl.Bignum.AddAndMultiply.fst \
	Hacl.Spec.MAC.Poly1305_64.fst \
	Hacl.MAC.Poly1305_64.fst

POLY1305_MODULES= \
	Hacl.Bignum.Parameters \
	Hacl.Bignum.Limb \
	Hacl.Bignum.Wide \
	Hacl.Spec.Bignum.Field \
	Hacl.Spec.Bignum.Bigint \
	Hacl.Bignum.Modulo \
	Hacl.Spec.Bignum.Fsum \
	Hacl.Spec.Bignum.Fproduct \
	Hacl.Bignum.Fsum \
	Hacl.Bignum.Fproduct \
	Hacl.Spec.Bignum.AddAndMultiply \
	Hacl.Spec.MAC.Poly1305_64 \
	Hacl.MAC.Poly1305


%.fst-verify: %.fst
	$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib --include ../bignum $^ --use_hints

verify: $(addsuffix -verify, $(POLY1305_FILES))

%.fst-hints: %.fst
	$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib --include ../bignum $^ --record_hints

hints: $(addsuffix -hints, $(POLY1305_SPECIFIC))


extract-c:
	mkdir -p poly-c
	$(KREMLIN_HOME)/krml -I $(FSTAR_HOME)/ulib/hyperstack -tmpdir poly-c -verbose \
		-I ../bignum -I ../lib/kremlin -I $(FSTAR_HOME)/../kremlin/kremlib -I $(FSTAR_HOME)/../kremlin/test \
		$(POLY1305_FILES) Hacl.Test.Poly1305_64.fst \
		-drop FStar -drop Hacl.Spec -drop Prims -drop Hacl.Cast -drop Hacl.UInt8 -drop Hacl.UInt32 -drop Hacl.UInt64 \
		-drop Hacl.UInt128  -drop Hacl.Bignum.Constants -drop Hacl.Bignum.Parameters -drop Hacl.Bignum.Limb -drop Hacl.Bignum.Wide \
		-bundle Hacl.Spec -bundle Hacl.Bignum -bundle Hacl.MAC \
		$(FSTAR_HOME)/../kremlin/test/testlib.c -add-include '"testlib.h"' \
		-ccopt -Wno-error=pointer-sign -ccopt -Wno-error=incompatible-pointer-types \
                -ccopt -Wno-error=format= -no-prefix Hacl.Test.Poly1305_64 -ccopt -flto -ccopt -march=native -o poly1305.exe
	./poly1305.exe


clean:
	rm -rf *.exe *.exe.* *.out *~ poly1305-c
