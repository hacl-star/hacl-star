FSTAR_HOME?=../../../dependencies/FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
HACL_HOME?=../..
include ../Makefile.include


X25519_FILES= \
	../bignum/Hacl.Bignum.Limb.fst \
	../bignum/Hacl.Bignum.Wide.fst \
	../bignum/Hacl.Spec.Bignum.Field.fst \
	../bignum/Hacl.Spec.Bignum.Bigint.fst \
	../bignum/Hacl.Spec.Bignum.Fsum.fst \
	../bignum/Hacl.Spec.Bignum.Fdifference.fst  \
	../bignum/Hacl.Spec.Bignum.Fscalar.fst \
	../bignum/Hacl.Spec.Bignum.Fproduct.fst \
	../bignum/Hacl.Bignum.Fsum.fst \
	../bignum/Hacl.Bignum.Fdifference.fst  \
	../bignum/Hacl.Bignum.Fscalar.fst \
	../bignum/Hacl.Bignum.Fproduct.fst \
	../bignum/Hacl.Bignum.fst \
	Hacl.Bignum.Constants.fst \
	Hacl.Bignum.Parameters.fst \
	Hacl.Spec.Bignum.Modulo.fst \
	Hacl.Bignum.Modulo.fst \
	Hacl.Spec.Bignum.Fsquare.fst \
	Hacl.Spec.EC.AddAndDouble.fst \
	Hacl.Spec.EC.AddAndDouble2.fst \
	Hacl.Bignum.Fsquare.fst \
	Hacl.Spec.EC.Point.fst \
	Hacl.EC.Point.fst \
	Hacl.EC.AddAndDouble.fst \
	Hacl.Spec.EC.Format.fst \
	Hacl.EC.Format.fst \
	Hacl.EC.Ladder.SmallLoop.fst \
	Hacl.EC.Ladder.BigLoop.fst \
	Hacl.EC.Ladder.fst \
	Hacl.EC.fst
#	Hacl.Spec.Bignum.Crecip.fst \
	Hacl.Bignum.Crecip.fst \

X25519_SPECIFIC= \
	Hacl.Spec.Bignum.Fsquare.fst \
	Hacl.Bignum.Constants.fst \
	Hacl.Bignum.Parameters.fst \
	Hacl.Spec.Bignum.Crecip.fst \
	Hacl.Bignum.Crecip.fst \
	Hacl.Spec.EC.AddAndDouble2.fst \
	Hacl.Bignum.Fsquare.fst \
	Hacl.Spec.Bignum.Modulo.fst \
	Hacl.Bignum.Modulo.fst \
	Hacl.Spec.EC.AddAndDouble.fst \
	Hacl.EC.AddAndDouble.fst \
	Hacl.Spec.EC.Point.fst \
	Hacl.EC.Point.fst \
	Hacl.Spec.EC.Format.fst \
	Hacl.EC.Format.fst \
	Hacl.Spec.EC.Ladder.fst \
	Hacl.EC.Ladder.fst \
	Hacl.Spec.EC.fst \
	Hacl.EC.fst

%.fst-verify: %.fst
	$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib --include ../bignum $^ --use_hints

verify: $(addsuffix -verify, $(X25519_FILES))

%.fst-hints: %.fst
	$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib --include ../bignum $^ --record_hints

hints: $(addsuffix -hints, $(X25519_SPECIFIC))

extract-c:
	# Weird \* because of https://caml.inria.fr/mantis/view.php?id=7473
	mkdir -p x25519-c
	$(KREMLIN_HOME)/krml -tmpdir x25519-c -verbose \
		-I ../bignum -I ../lib/kremlin \
		Curve25519.fst Hacl.Test.X25519.fst \
		-drop 'Hacl.Spec.\*' -drop 'Hacl.Cast' -drop 'Hacl.UInt.\*' \
		-drop Prims -drop FStar -bundle 'Curve25519=Hacl.Bignum.*,Hacl.EC.*' \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' \
                -no-prefix Hacl.Test.X25519 -ldopt -flto -ccopt -march=native -o x25519.exe
	./x25519.exe

clean:
	rm -rf *.exe *.exe.* *.out *~ x25519-c 
