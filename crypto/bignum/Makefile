
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


x25519-parameters:
	$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include x25519 \
		--include ../../lib/hyperstack --explicit_deps $(FSTAR_LIB_FILES) $(HACL_LIB_FILES) \
		 Hacl.Bignum.Parameters.fsti Hacl.Bignum.Parameters.fst \
		--verify_module Hacl.Bignum.Parameters


x25519-limb:
	$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include x25519 --detail_errors --print_before_norm \
		--include ../../lib/hyperstack --explicit_deps $(FSTAR_LIB_FILES) $(HACL_LIB_FILES) \
		Hacl.Bignum.Parameters.fsti Hacl.Bignum.Parameters.fst \
		Hacl.Bignum.Limb.fsti Hacl.Bignum.Limb.fst \
		--verify_module Hacl.Bignum.Limb
