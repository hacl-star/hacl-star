
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

test:
	mkdir -p tmp
	$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack --lax --odir tmp \
		--include x25519 --codegen Kremlin \
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
		Hacl.EC.fst


kremlin:
	mkdir -p tmp
	krml -I $(FSTAR_HOME)/ulib/hyperstack -tmpdir tmp -verbose \
		-I x25519 \
		-I ../../lib/hyperstack/kremlin \
		Hacl.Bignum.Constants.fst \
		Hacl.Bignum.Parameters.fst \
		Hacl.Bignum.Limb.fst Hacl.Bignum.Wide.fst \
		Hacl.Bignum.Bigint.fst \
		Hacl.Bignum.Modulo.fst \
		Hacl.Bignum.Predicates.fst \
		Hacl.Bignum.Fsum.Spec.fst Hacl.Bignum.Fdifference.Spec.fst  \
		Hacl.Bignum.Fscalar.Spec.fst Hacl.Bignum.Fproduct.Spec.fst \
		Hacl.Bignum.Fsum.fst Hacl.Bignum.Fdifference.fst  \
		Hacl.Bignum.Fscalar.fst Hacl.Bignum.Fproduct.fst \
		Hacl.Bignum.Crecip.fst Hacl.Bignum.fst \
		Hacl.EC.Point.fst \
		Hacl.EC.AddAndDouble.fst \
		Hacl.EC.Format.fst \
		Hacl.EC.Ladder.fst \
		Hacl.EC.fst \
		Hacl.Test.X25519.fst \
		-I $(FSTAR_HOME)/../kremlin/kremlib -I $(FSTAR_HOME)/../kremlin/test \
		$(FSTAR_HOME)/../kremlin/test/testlib.c -add-include '"testlib.h"' \
		-ccopt -Wno-error=pointer-sign -ccopt -Wno-error=incompatible-pointer-types \
                -ccopt -Wno-error=format= -no-prefix Hacl.Test.X25519

compile:
	gcc -Wall -Werror -Wno-parentheses -Wno-unused-variable -g -O3 -fwrapv -I FSTAR_HOME/ulib/hyperstack -I /home/jkz/dev/FStar/ulib/hyperstack -I x25519 -I ../../lib/hyperstack/kremlin -I /home/jkz/dev/FStar/../kremlin/kremlib -I /home/jkz/dev/FStar/../kremlin/test -I /home/jkz/dev/kremlin/kremlib -I tmp -Wno-error=pointer-sign -Wno-error=incompatible-pointer-types -Wno-error=format= \
		tmp/Prims.c \
		tmp/FStar_Mul.c \
		tmp/FStar_Squash.c \
		tmp/FStar_StrongExcludedMiddle.c \
		tmp/FStar_List_Tot.c \
		tmp/FStar_Classical.c \
		tmp/FStar_ListProperties.c \
		tmp/FStar_SeqProperties.c \
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
		tmp/FStar_Ghost.c \
		tmp/FStar_All.c \
		tmp/Hacl_UInt64.c \
		tmp/Hacl_UInt128.c \
		tmp/Hacl_UInt32.c \
		tmp/Hacl_UInt8.c \
		tmp/Hacl_Cast.c \
		tmp/Hacl_Bignum_Constants.c \
		tmp/FStar_Buffer.c \
		tmp/Hacl_Bignum_Parameters.c \
		tmp/Hacl_Bignum_Predicates.c \
		tmp/Hacl_Bignum_Limb.c \
		tmp/Hacl_Bignum_Wide.c \
		tmp/Hacl_Bignum_Bigint.c \
		tmp/Hacl_Bignum_Fsum_Spec.c \
		tmp/Hacl_Bignum_Fsum.c \
		tmp/Hacl_Bignum_Fscalar_Spec.c \
		tmp/Hacl_Bignum_Modulo.c \
		tmp/Hacl_Bignum_Fproduct_Spec.c \
		tmp/Hacl_Bignum_Fdifference_Spec.c \
		tmp/Hacl_Bignum_Fproduct.c \
		tmp/Hacl_Bignum_Crecip.c \
		tmp/Hacl_Bignum_Fdifference.c \
		tmp/Hacl_Bignum_Fscalar.c \
		tmp/Hacl_Bignum.c \
		tmp/Hacl_EC_Point.c \
		tmp/Hacl_EC_Format.c \
		tmp/Hacl_EC_AddAndDouble.c \
		tmp/Hacl_EC_Ladder.c \
		tmp/Hacl_EC.c \
		tmp/Hacl_Test_X25519.c \
		/home/jkz/dev/kremlin/kremlib/kremlib.c \
		/home/jkz/dev/FStar/../kremlin/test/testlib.c
