FSTAR_HOME?=../../../dependencies/FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
HACL_HOME?=../../..
include ../../../code/Makefile.include

FILE=Hacl.Bignum.Fsum.fst

verify:
	$(FSTAR_HOME)/bin/fstar.exe  \
		--include ../../../code/bignum --include ../../../code/curve25519 \
		--include ../../../code/lib/kremlin $(FILE)

extract:
	mkdir -p extracted_c
	$(KREMLIN_HOME)/krml  -tmpdir extracted_c -verbose \
		-I ../../../code/bignum -I ../../../code/curve25519 -I ../../../code/lib/kremlin \
		$(FILE) -drop FStar -drop Prims -drop Hacl.Cast -drop Hacl.UInt8 -drop Hacl.UInt32 -drop Hacl.UInt64 \
		-drop Hacl.UInt128  -drop Hacl.Bignum.Constants -drop Hacl.Bignum.Parameters -drop Hacl.Bignum.Limb -drop Hacl.Bignum.Wide -drop Hacl.Spec.Bignum.Field -drop Hacl.Spec.Bignum.Bigint \
		-skip-compilation

clean:
	rm -rf *~ extracted_c
