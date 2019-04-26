include ../../../Makefile.include

FSTAR_LIB_FILES= \
	FStar.Mul.fst \
	FStar.Squash.fsti \
	FStar.Squash.fst \
	FStar.Classical.fst \
	FStar.StrongExcludedMiddle.fst \
	FStar.PropositionalExtensionality.fst \
	FStar.FunctionalExtensionality.fst \
	FStar.PredicateExtensionality.fst \
	FStar.List.Tot.Base.fst \
	FStar.List.Tot.Properties.fst \
	FStar.List.Tot.fst \
	FStar.Seq.Base.fst \
	FStar.Seq.Properties.fst \
	FStar.Seq.fst \
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
	$(FSTAR_HOME)/bin/fstar.exe \
		--include ../../lib --include ../../bignum $^ --use_hints

verify: $(addsuffix -verify, $(POLY1305_FILES))

%.fst-hints: %.fst
	$(FSTAR_HOME)/bin/fstar.exe \
		--include ../../lib --include ../../bignum $^ --record_hints

hints: $(addsuffix -hints, $(POLY1305_SPECIFIC))


extract-c:
	mkdir -p poly-c
	$(KREMLIN_HOME)/krml -tmpdir poly-c -verbose \
		-I ../../bignum -I ../../lib/kremlin -I $(KREMLIN_HOME)/kremlib/compat \
		Hacl.Test.Poly1305_32.fst \
		-drop FStar -drop Hacl.Spec -drop Prims -drop Hacl.Cast -drop Hacl.UInt8 -drop Hacl.UInt32 -drop Hacl.UInt64 \
		-drop Hacl.UInt128  -drop Hacl.Bignum.Constants -drop Hacl.Bignum.Parameters -drop Hacl.Bignum.Limb -drop Hacl.Bignum.Wide \
		-bundle "Hacl.Spec.\*" -bundle "Poly1305_32=Poly1305_32,Hacl.Bignum.\*,Hacl.MAC.\*" \
		-add-include '"testlib.h"' $(KREMLIN_HOME)/kremlib/c/testlib.c \
		-ccopt "-D_GNU_SOURCE" \
		-ccopt -Wno-error=pointer-sign -ccopt -Wno-error=incompatible-pointer-types \
                -ccopt -Wno-error=format= -no-prefix Hacl.Test.Poly1305_32 -ccopt -flto -ccopt -march=native -o poly1305.exe
	./poly1305.exe


include $(FSTAR_HOME)/src/gmake/fstar.mk
CODEGEN_ARGS=--lax --codegen OCaml --no_location_info $(FSTAR_DEFAULT_ARGS)
OCAMLOPT := $(OCAMLOPT) -w -8-20-26-28-10
POLY_EXTRACTED=Hacl_Bignum_Constants.ml Hacl_Bignum_Parameters.ml Hacl_MAC_Poly1305_64.ml

extract-ml:
	mkdir -p poly-ml
	$(FSTAR) $(CODEGEN_ARGS) --include ../bignum --include ../lib \
	--odir poly-ml $(POLY1305_FILES) \
	--no_extract Hacl.UInt64 --no_extract Hacl.UInt32 --no_extract Hacl.UInt128 --no_extract Hacl.UInt16 --trace_error
	$(OCAMLOPT) -I poly-ml  -I ../lib/ml $(addprefix poly-ml/,$(POLY_EXTRACTED))

compile-ml:
	$(OCAMLOPT) -I poly-ml -I ../lib/ml $(addprefix poly-ml/,$(POLY_EXTRACTED))

clean:
	rm -rf *.exe *.exe.* *.out *~ poly-c
