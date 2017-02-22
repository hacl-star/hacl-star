FSTAR_HOME?=../../../dependencies/FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
HACL_HOME?=../..
include ../Makefile.include


BIGNUM_FILES= \
	Hacl.Bignum.Limb.fst \
	Hacl.Bignum.Wide.fst \
	Hacl.Spec.Bignum.Field.fst \
	Hacl.Spec.Bignum.Bigint.fst \
	Hacl.Spec.Bignum.Fsum.fst \
	Hacl.Spec.Bignum.Fdifference.fst  \
	Hacl.Spec.Bignum.Fscalar.fst \
	Hacl.Spec.Bignum.Fproduct.fst \
	Hacl.Spec.Bignum.Fmul.fst \
	Hacl.Spec.Bignum.fst \
	Hacl.Bignum.Fsum.fst \
	Hacl.Bignum.Fdifference.fst  \
	Hacl.Bignum.Fscalar.fst \
	Hacl.Bignum.Fproduct.fst \
	Hacl.Bignum.Fmul.fst \
	Hacl.Bignum.fst 
#	Hacl.Bignum.Constants.fsti \
	Hacl.Bignum.Parameters.fsti \
	Hacl.Bignum.Modulo.fsti \
	Hacl.Bignum.Crecip.fsti \

BIGNUM_MODULES=$(basename $(BIGNUM_FILES))

%.fst-ct: %.fst
	$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack --include interfaces \
		--include ../lib $^ --lax

all-ct: $(addsuffix -ct, $(BIGNUM_FILES))

%.fst-verify: %.fst
	$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack --include interfaces \
		--include ../lib $^ --use_hints --record_hints

verify: $(addsuffix -verify, $(BIGNUM_FILES))

all-ci: verify

%-hints: %.fst
	-$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack --include interfaces \
		--include ../lib $^ --record_hints --use_hints

ALL_HINTS=$(addsuffix -hints, $(BIGNUM_MODULES))

all-hints: $(ALL_HINTS)

clean:
	rm -rf *.exe *.out *~ x25519/*~ poly1305/*~ interfaces/*~ tmp tmppoly
