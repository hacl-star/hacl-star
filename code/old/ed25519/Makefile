include ../Makefile.include

BIGNUM= \
	../bignum/Hacl.Bignum.Limb.fst \
	../bignum/Hacl.Bignum.Wide.fst \
	../bignum/Hacl.Bignum.Fsum.fst \
	../bignum/Hacl.Bignum.Fproduct.fst \
	../bignum/Hacl.Bignum.Fmul.fst \
	../bignum/Hacl.Spec.Bignum.Field.fst \
	../bignum/Hacl.Spec.Bignum.Bigint.fst \
	../bignum/Hacl.Spec.Bignum.Fsum.fst \
	../bignum/Hacl.Spec.Bignum.Fproduct.fst \
	../bignum/Hacl.Spec.Bignum.Fmul.fst

ED25519_SPECIFIC= \
	Hacl.Impl.BignumQ.Mul.fst \
	Hacl.Spec.BignumQ.Mul.fst \
	Hacl.Lib.Create64.fst \
	Hacl.Bignum25519.fsti \
	Hacl.Bignum25519.fst \
	Hacl.Impl.Ed25519.ExtPoint.fst \
	Hacl.Impl.Ed25519.SwapConditional.fst \
	Hacl.Impl.Ed25519.PointDouble.fsti \
	Hacl.Impl.Ed25519.PointDouble.fst \
	Hacl.Impl.Ed25519.PointAdd.fsti \
	Hacl.Impl.Ed25519.PointAdd.fst \
	Hacl.Impl.Ed25519.Ladder.Step.fsti \
	Hacl.Impl.Ed25519.Ladder.Step.fst \
	Hacl.Impl.Ed25519.Ladder.fsti \
	Hacl.Impl.Ed25519.Ladder.fst \
	Hacl.Impl.Ed25519.PointCompress.fst \
	Hacl.Impl.Ed25519.G.fst \
	Hacl.Impl.Ed25519.SecretExpand.fsti \
	Hacl.Impl.Ed25519.SecretExpand.fst \
	Hacl.Spec.BignumQ.Eval.fst \
	Hacl.Spec.BignumQ.Mul.Lemmas_1.fst \
	Hacl.Spec.BignumQ.Mul.Lemmas_3.fst \
	Spec.BarrettReduction.fst \
	Hacl.Lib.Create128.fst \
	Hacl.Impl.BignumQ.Mul.fsti \
	Hacl.Impl.Sha512.fst \
	Hacl.Impl.Load56.fsti \
	Hacl.Impl.Load56.fst \
	Hacl.Impl.SHA512.ModQ.fsti \
	Hacl.Impl.SHA512.ModQ.fst \
	Hacl.Impl.Store56.fst \
	Hacl.Impl.Ed25519.Sign.Steps.fst \
	Hacl.Impl.Ed25519.Sign.fst \
	Hacl.Impl.Ed25519.Sign.Expanded.fst \
	Hacl.Impl.Load51.fsti \
	Hacl.Impl.Load51.fst \
	Hacl.Impl.Ed25519.Pow2_252m2.fsti \
	Hacl.Impl.Ed25519.Pow2_252m2.fst \
	Hacl.Impl.Ed25519.RecoverX.fsti \
	Hacl.Impl.Ed25519.RecoverX.fst \
	Hacl.Impl.Ed25519.PointDecompress.fsti \
	Hacl.Impl.Ed25519.PointDecompress.fst \
	Hacl.Impl.Ed25519.Verify.Lemmas.fst \
	Hacl.Impl.Ed25519.PointEqual.fsti \
	Hacl.Impl.Ed25519.PointEqual.fst \
	Hacl.Impl.Ed25519.Verify.Steps.fst \
	Hacl.Impl.Ed25519.Verify.fst \
	Hacl.Impl.Ed25519.SecretToPublic.fsti \
	Hacl.Impl.Ed25519.SecretToPublic.fst \
	Hacl.Ed25519.fsti \
	Hacl.Ed25519.fst

FSTS=   Hacl.Bignum25519.fst \
	../hash/Hacl.Impl.SHA512.Ed25519.fst \
	../hash/Hacl.SHA2_512.fst \
	Hacl.Impl.Load56.fst \
	Hacl.Impl.Load51.fst \
	Hacl.Impl.BignumQ.Mul.fst \
	Hacl.Impl.SHA512.ModQ.fst \
	Hacl.Impl.Sha512.fst \
	Hacl.Impl.Ed25519.Pow2_252m2.fst \
	Hacl.Impl.Ed25519.PointAdd.fst \
	Hacl.Impl.Ed25519.PointDouble.fst \
	Hacl.Impl.Ed25519.SecretExpand.fst \
	Hacl.Impl.Ed25519.PointCompress.fst \
	Hacl.Impl.Ed25519.PointDecompress.fst \
	Hacl.Impl.Ed25519.RecoverX.fst \
	Hacl.Impl.Ed25519.Ladder.Step.fst \
	Hacl.Impl.Ed25519.Ladder.fst \
	Hacl.Impl.Ed25519.PointEqual.fst \
	Hacl.Impl.Ed25519.SecretToPublic.fst \
	Hacl.Ed25519.fst \
	Hacl.Test.Ed25519.fst

# Files that are too slow and for which verification speed must improve
SLOW=

# Files that still have errors
TODO=

ED25519_FILES=$(ED25519_SPECIFIC) $(BIGNUM)

FSTAR_INCLUDES+=--include $(HACL_HOME)/code/bignum --include $(HACL_HOME)/code/curve25519 --include $(HACL_HOME)/code/hash

# Parameter for interactive mode
%.fst-in:
	@echo $(OPTIONS) --hint_info \
	$(FSTAR_INCLUDES)

ct: $(addsuffix -lax, $(ED25519_FILES))
	$(FSTAR) --lax --verify_all Hacl.Impl.Ed25519.SecretToPublic.fst Hacl.Impl.Ed25519.Sign.fst Hacl.Impl.Ed25519.Sign.Exanded.fst
all-ct: ct

bignum-ver: $(addsuffix -reloc-verify, $(BIGNUM))
specific-ver: $(addsuffix -verify, $(filter-out $(SLOW) $(TODO), $(ED25519_SPECIFIC)))
verify: bignum-ver specific-ver
hints: bignum-hints specific-hints
all-ver: verify

# Hints regeneration
bignum-hints: $(addsuffix .reloc.hints, $(BIGNUM))
specific-hints: $(addsuffix .hints, $(ED25519_SPECIFIC))
hints: bignum-hints specific-hints
all-hints: hints

# For CI, all modules restricted from incomplete or slow ones
bignum-ci: $(addsuffix -reloc-verify, $(filter-out $(SLOW) $(TODO), $(BIGNUM)))
specific-ci: $(addsuffix -verify, $(filter-out $(SLOW) $(TODO), $(ED25519_SPECIFIC)))
ci: bignum-ci specific-ci
all-ci: ci

KREMLIN_ARGS+= \
		-I ../bignum -I ../curve25519 -I ../hash \

ed25519-c/out.krml: $(ED25519_FILES)
	 $(KREMLIN) -verbose -tmpdir ed25519-c $(KREMLIN_ARGS) $(FSTS) -skip-translation

ed25519-c/Hacl_Ed25519.c: ed25519-c/out.krml
	 $(KREMLIN) -tmpdir ed25519-c $(KREMLIN_ARGS) \
		-bundle 'Hacl.Ed25519=*' -minimal -add-include '"kremlib.h"' \
		-skip-compilation $^ -o $@

ed25519-c89/Hacl_Ed25519.c: ed25519-c/out.krml
	 $(KREMLIN) -tmpdir ed25519-c89 -fc89 $(KREMLIN_ARGS) \
		-bundle 'Hacl.Ed25519=*' -minimal -add-include '"kremlib.h"' \
		-skip-compilation $^ -o $@

extract-c: ed25519-c89/Hacl_Ed25519.c ed25519-c/Hacl_Ed25519.c

ed25519.exe: ed25519-c/Hacl_Ed25519.c ed25519-c/out.krml
	$(KREMLIN) -tmpdir ed25519-c $(KREMLIN_ARGS) \
	  -no-prefix 'Hacl.Test.Ed25519' -minimal -add-include '"kremlib.h"' \
	  -bundle 'Hacl.Test.Ed25519=*' -library Hacl.Ed25519 \
	  $^ -o $@


test: ed25519.exe
	./$^

count-line:
	cloc --force-lang=ocaml $(ED25519_FILES)

clean:
	rm -rf *.exe *.exe.* *.out *~ ed25519-c *.graph
