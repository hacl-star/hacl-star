include ../Makefile.include

# Verify everything with the used parameters
BIGNUM= \
	../bignum/Hacl.Bignum.Fdifference.fst \
	../bignum/Hacl.Bignum.Fmul.fst \
	../bignum/Hacl.Bignum.Fproduct.fst \
	../bignum/Hacl.Bignum.Fscalar.fst \
	../bignum/Hacl.Bignum.Fsum.fst \
	../bignum/Hacl.Bignum.Limb.fst \
	../bignum/Hacl.Bignum.Wide.fst \
	../bignum/Hacl.Bignum.fst \
	../bignum/Hacl.Spec.Bignum.Bigint.fst \
	../bignum/Hacl.Spec.Bignum.Fdifference.fst \
	../bignum/Hacl.Spec.Bignum.Field.fst \
	../bignum/Hacl.Spec.Bignum.Fmul.fst \
	../bignum/Hacl.Spec.Bignum.Fproduct.fst \
	../bignum/Hacl.Spec.Bignum.Fscalar.fst \
	../bignum/Hacl.Spec.Bignum.Fsum.fst \
	../bignum/Hacl.Spec.Bignum.fst

X25519_SPECIFIC= \
	Hacl.Spec.Curve25519.Lemmas.fst \
	Hacl.Bignum.Parameters.fst \
	Hacl.Spec.Bignum.Modulo.fst \
	Hacl.Spec.EC.AddAndDouble.fst \
	Hacl.Spec.Bignum.Fsquare.fst \
	Hacl.Spec.Bignum.Crecip.fst \
	Hacl.Bignum.Modulo.fst \
	Hacl.Bignum.Fsquare.fst \
	Hacl.Bignum.Crecip.fst \
	Hacl.Spec.EC.Point.fst \
	Hacl.EC.Point.fst \
	Hacl.Spec.EC.AddAndDouble2.fst \
	Hacl.Spec.EC.AddAndDouble3.fst \
	Hacl.Spec.EC.Format.Lemmas.fst \
	Hacl.Spec.EC.Format.fst \
	Hacl.EC.Format.fst \
	Hacl.EC.AddAndDouble.fst \
	Hacl.Spec.EC.Ladder.Lemmas.fst \
	Hacl.Spec.EC.Ladder.fst \
	Hacl.EC.Ladder.SmallLoop.fst \
	Hacl.EC.Ladder.BigLoop.fst \
	Hacl.EC.Ladder.fst \
	Hacl.Spec.EC.fst \
	Hacl.EC.fst \
	Hacl.Curve25519.fst

# Files that are too slow and for which verification speed must improve
SLOW=

X25519_FILES=$(BIGNUM) $(X25519_SPECIFIC)

FSTAR_INCLUDES+=--include ../bignum

# Parameters for interactive mode
%.fst-in:
	@echo $(OPTIONS) --hint_info \
	$(FSTAR_INCLUDES)

ct: $(addsuffix -lax, $(X25519_FILES))
	# Using the --verify_all argument to lift abstractions, typechecks all dependencies of Curve25519.fst
	$(FSTAR) --lax --verify_all Hacl.Curve25519.fst

bignum-ver: $(addsuffix -reloc-verify, $(BIGNUM))
specific-ver: $(addsuffix -verify, $(X25519_SPECIFIC))
verify: bignum-ver specific-ver
all-ver: verify
all-ct: ct

# Hints regeneration
bignum-hints: $(addsuffix .reloc.hints, $(BIGNUM))
specific-hints: $(addsuffix .hints, $(X25519_SPECIFIC))
hints: bignum-hints specific-hints
all-hints: hints

# For CI, all modules restricted from incomplete or slow ones
bignum-ci: $(addsuffix -reloc-verify, $(filter-out $(SLOW), $(BIGNUM)))
specific-ci: $(addsuffix -verify, $(filter-out $(SLOW), $(X25519_SPECIFIC)))
all-ci: bignum-ci specific-ci


CFLAGS=-Wall -Wextra -Wno-unused-parameter -Wno-unused-variable
KREMLIN_ARGS+= -I ../bignum \
	$(KREMLIN_TESTLIB)

# Acknowledge the F* dependency graph
.PHONY: depend
depend:
	$(FSTAR) --dep make $(X25519_FILES) > .depend
-include .depend

x25519-c/out.krml: $(X25519_FILES) Hacl.Test.X25519.fst
	$(KREMLIN) -tmpdir x25519-c $(KREMLIN_ARGS) -skip-translation $^ -o $@

x25519-c/Hacl_Test_X25519.c: x25519-c/Hacl_Curve25519.c

x25519-c/Hacl_Curve25519.c:  x25519-c/out.krml
	$(KREMLIN) -tmpdir x25519-c $(KREMLIN_ARGS) \
	 	-bundle 'Hacl.Curve25519=*' \
		-minimal -add-include '"kremlib.h"' \
		-skip-compilation $^ -o $@

x25519-c89/Hacl_Curve25519.c:  x25519-c/out.krml
	$(KREMLIN) -tmpdir x25519-c89 $(KREMLIN_ARGS) \
	 	-bundle 'Hacl.Curve25519=*' \
		-minimal -add-include '"kremlib.h"' \
		-skip-compilation $^ -o $@ -fc89

x25519.exe: x25519-c/Hacl_Curve25519.c x25519-c/out.krml
	$(KREMLIN) -tmpdir x25519-c $(KREMLIN_ARGS) -no-prefix Hacl.Test.X25519 \
	 	-bundle 'Hacl.Test.X25519=*' \
		-minimal -add-include '"kremlib.h"' \
		$^ -o $@
	./$@

extract-c: x25519-c89/Hacl_Curve25519.c x25519-c/Hacl_Curve25519.c x25519-c/Hacl_Test_X25519.c

test: x25519.exe

X25519_LIB= \
	Hacl.Bignum.Parameters.fst \
	Hacl.Spec.Bignum.Modulo.fst \
	Hacl.Spec.EC.AddAndDouble.fst \
	Hacl.Spec.Bignum.Fsquare.fst \
	Hacl.Spec.Bignum.Crecip.fst \
	Hacl.Bignum.Modulo.fst \
	Hacl.Bignum.Fsquare.fst \
	Hacl.Bignum.Crecip.fst \
	Hacl.EC.Point.fst \
	Hacl.Spec.EC.Format.Lemmas.fst \
	Hacl.Spec.EC.Format.fst \
	Hacl.EC.Format.fst \


X25519_ONLY=Hacl.Spec.EC.Point.fst \
	Hacl.Spec.Curve25519.Lemmas.fst \
	Hacl.Spec.EC.AddAndDouble2.fst \
	Hacl.EC.AddAndDouble.fst \
	Hacl.Spec.EC.Ladder.Lemmas.fst \
	Hacl.Spec.EC.Ladder.fst \
	Hacl.EC.Ladder.SmallLoop.fst \
	Hacl.EC.Ladder.BigLoop.fst \
	Hacl.EC.Ladder.fst \
	Hacl.Spec.EC.fst \
	Hacl.EC.fst

count-line:
	@echo "X25519 LIB LOC"
	cloc --force-lang=ocaml $(X25519_LIB)
	@echo "X25519 ONLY LOC"
	cloc --force-lang=ocaml $(X25519_ONLY)

clean:
	rm -rf *.exe *.exe.* *.out *~ x25519-c
