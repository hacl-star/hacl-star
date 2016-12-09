
FSTAR_HOME?=../../../FStar
KREMLIN_HOME=$(FSTAR_HOME)/../kremlin
HACL_HOME=../..
include ../../lib/hyperstack/Makefile.include


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
	FStar.UInt.fst \
	FStar.UInt32.fst \
	FStar.UInt8.fst \
	FStar.UInt64.fst \
	FStar.UInt128.fst \
	FStar.TSet.fst \
	FStar.Set.fst \
	FStar.Map.fst \
	FStar.Heap.fst \
	FStar.Ghost.fst \
	FStar.HyperHeap.fst \
	FStar.HyperStack.fst \
	FStar.ST.fst \
	FStar.Buffer.fst


HACL_LIB_FILES= Hacl.UInt8.fst Hacl.UInt32.fst Hacl.UInt64.fst Hacl.UInt128.fst Hacl.Cast.fst 


# x25519-parameters:
# 	$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
# 		--include x25519 \
# 		--include ../../lib/hyperstack --explicit_deps $(FSTAR_LIB_FILES) $(HACL_LIB_FILES) \
# 		Hacl.Bignum.Constants.fst \
# 		 Hacl.Bignum.Parameters.fsti Hacl.Bignum.Parameters.fst \
# 		--verify_module Hacl.Bignum.Parameters

# x25519-limb:
# 	$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
# 		--include x25519 --detail_errors --print_before_norm \
# 		--include ../../lib/hyperstack --explicit_deps $(FSTAR_LIB_FILES) $(HACL_LIB_FILES) \
# 		Hacl.Bignum.Parameters.fsti Hacl.Bignum.Parameters.fst \
# 		Hacl.Bignum.Limb.fst \
# 		--verify_module Hacl.Bignum.Limb

# x25519-wide:
# 	$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
# 		--include x25519 --detail_errors --print_before_norm \
# 		--include ../../lib/hyperstack --explicit_deps $(FSTAR_LIB_FILES) $(HACL_LIB_FILES) \
# 		Hacl.Bignum.Parameters.fsti Hacl.Bignum.Parameters.fst \
# 		Hacl.Bignum.Wide.fst \
# 		--verify_module Hacl.Bignum.Wide

bignum:
	$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../../lib/hyperstack --explicit_deps $(FSTAR_LIB_FILES) $(HACL_LIB_FILES) \
		generic/Hacl.Bignum.Constants.fsti \
		Hacl.Bignum.Parameters.fsti Hacl.Bignum.Limb.fst Hacl.Bignum.Wide.fst \
		Hacl.Bignum.Bigint.fst \
		Hacl.Bignum.Modulo.fsti \
		Hacl.Bignum.Predicates.fsti \
		Hacl.Bignum.Fsum.Spec.fst Hacl.Bignum.Fdifference.Spec.fst  \
		Hacl.Bignum.Fscalar.Spec.fst Hacl.Bignum.Fproduct.Spec.fst \
		Hacl.Bignum.Fsum.fst Hacl.Bignum.Fdifference.fst  \
		Hacl.Bignum.Fscalar.fst Hacl.Bignum.Fproduct.fst \
		Hacl.Bignum.Crecip.fsti Hacl.Bignum.fst \
		$(addprefix --verify_module , 	Hacl.Bignum.Parameters \
						Hacl.Bignum.Limb \
						Hacl.Bignum.Wide \
						Hacl.Bignum.Bigint \
						Hacl.Bignum.Modulo \
						Hacl.Bignum.Fsum.Spec \
						Hacl.Bignum.Fdifference.Spec \
						Hacl.Bignum.Fscalar.Spec \
						Hacl.Bignum.Fproduct.Spec \
						Hacl.Bignum.Fsum \
						Hacl.Bignum.Fdifference \
						Hacl.Bignum.Fscalar \
						Hacl.Bignum.Fproduct \
						Hacl.Bignum.Crecip \
						Hacl.Bignum.Predicates \
						Hacl.Bignum \
		)

x25519-bignum:
	$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include x25519  \
		--include ../../lib/hyperstack --explicit_deps $(FSTAR_LIB_FILES) $(HACL_LIB_FILES) \
		Hacl.Bignum.Constants.fst \
		Hacl.Bignum.Parameters.fsti Hacl.Bignum.Parameters.fst \
		Hacl.Bignum.Limb.fst Hacl.Bignum.Wide.fst \
		Hacl.Bignum.Bigint.fst \
		Hacl.Bignum.Modulo.fsti Hacl.Bignum.Modulo.fst \
		Hacl.Bignum.Predicates.fsti Hacl.Bignum.Predicates.fst \
		Hacl.Bignum.Fsum.Spec.fst Hacl.Bignum.Fdifference.Spec.fst  \
		Hacl.Bignum.Fscalar.Spec.fst Hacl.Bignum.Fproduct.Spec.fst \
		Hacl.Bignum.Fsum.fst Hacl.Bignum.Fdifference.fst  \
		Hacl.Bignum.Fscalar.fst Hacl.Bignum.Fproduct.fst \
		Hacl.Bignum.Crecip.fsti Hacl.Bignum.Crecip.fst Hacl.Bignum.fst \
		$(addprefix --verify_module , 	Hacl.Bignum.Parameters \
						Hacl.Bignum.Limb \
						Hacl.Bignum.Wide \
						Hacl.Bignum.Bigint \
						Hacl.Bignum.Modulo \
						Hacl.Bignum.Fsum.Spec \
						Hacl.Bignum.Fdifference.Spec \
						Hacl.Bignum.Fscalar.Spec \
						Hacl.Bignum.Fproduct.Spec \
						Hacl.Bignum.Fsum \
						Hacl.Bignum.Fdifference \
						Hacl.Bignum.Fscalar \
						Hacl.Bignum.Fproduct \
						Hacl.Bignum.Crecip \
						Hacl.Bignum.Predicates \
						Hacl.Bignum \
		)


.PHONY:x25519

x25519:
	$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack --lax \
		--include x25519  \
		--include ../../lib/hyperstack --explicit_deps $(FSTAR_LIB_FILES) $(HACL_LIB_FILES) \
		Hacl.Bignum.Constants.fst \
		Hacl.Bignum.Parameters.fsti Hacl.Bignum.Parameters.fst \
		Hacl.Bignum.Limb.fst Hacl.Bignum.Wide.fst \
		Hacl.Bignum.Bigint.fst \
		Hacl.Bignum.Modulo.fsti Hacl.Bignum.Modulo.fst \
		Hacl.Bignum.Predicates.fsti Hacl.Bignum.Predicates.fst \
		Hacl.Bignum.Fsum.Spec.fst Hacl.Bignum.Fdifference.Spec.fst  \
		Hacl.Bignum.Fscalar.Spec.fst Hacl.Bignum.Fproduct.Spec.fst \
		Hacl.Bignum.Fsum.fst Hacl.Bignum.Fdifference.fst  \
		Hacl.Bignum.Fscalar.fst Hacl.Bignum.Fproduct.fst \
		Hacl.Bignum.Crecip.fsti Hacl.Bignum.Crecip.fst Hacl.Bignum.fst \
		Hacl.EC.Point.fsti Hacl.EC.Point.fst \
		Hacl.EC.AddAndDouble.fsti Hacl.EC.AddAndDouble.fst \
		Hacl.EC.Format.fsti Hacl.EC.Format.fst \
		Hacl.EC.Ladder.fst \
		Hacl.EC.fst \
		$(addprefix --verify_module , 	Hacl.Bignum.Parameters \
						Hacl.Bignum.Limb \
						Hacl.Bignum.Wide \
						Hacl.Bignum.Bigint \
						Hacl.Bignum.Modulo \
						Hacl.Bignum.Fsum.Spec \
						Hacl.Bignum.Fdifference.Spec \
						Hacl.Bignum.Fscalar.Spec \
						Hacl.Bignum.Fproduct.Spec \
						Hacl.Bignum.Fsum \
						Hacl.Bignum.Fdifference \
						Hacl.Bignum.Fscalar \
						Hacl.Bignum.Fproduct \
						Hacl.Bignum.Crecip \
						Hacl.Bignum.Predicates \
						Hacl.Bignum \
						Hacl.EC.Point \
						Hacl.EC.AddAndDouble \
						Hacl.EC.Ladder \
						Hacl.EC.Format \
						Hacl.EC \
		)
