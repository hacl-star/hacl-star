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

FSTAR_INCLUDES+=--include interfaces --include ../lib

ct: $(addsuffix -lax, $(BIGNUM_FILES))
verify: $(addsuffix -verify, $(BIGNUM_FILES))
hints: $(addsuffix .hints, $(BIGNUM_FILES))
test:

all-ci: verify
all-ver: verify
all-hints: hints
all-ct: ct

count-line:
	cloc --force-lang=ocaml $(BIGNUM_FILES)

clean:
	rm -rf *.exe *.out *~ x25519/*~ poly1305/*~ interfaces/*~ tmp tmppoly
