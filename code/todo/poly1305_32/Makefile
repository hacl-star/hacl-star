include ../../Makefile.include

BIGNUM= \
	$(HACL_HOME)/code/bignum/Hacl.Spec.Bignum.Field.fst \
	$(HACL_HOME)/code/bignum/Hacl.Bignum.Limb.fst \
	$(HACL_HOME)/code/bignum/Hacl.Bignum.Wide.fst \
	$(HACL_HOME)/code/bignum/Hacl.Spec.Bignum.Bigint.fst \
	$(HACL_HOME)/code/bignum/Hacl.Spec.Bignum.Fsum.fst \
	$(HACL_HOME)/code/bignum/Hacl.Spec.Bignum.Fproduct.fst \
	$(HACL_HOME)/code/bignum/Hacl.Spec.Bignum.Fmul.fst \
	$(HACL_HOME)/code/bignum/Hacl.Bignum.Fsum.fst \
	$(HACL_HOME)/code/bignum/Hacl.Bignum.Fproduct.fst \
	$(HACL_HOME)/code/bignum/Hacl.Bignum.Fmul.fst \

POLY1305_SPECIFIC= \
	Hacl.Bignum.Constants.fst \
	Hacl.Bignum.Parameters.fst \
	Hacl.Spec.Bignum.Modulo.fst \
	Hacl.Spec.Bignum.AddAndMultiply.fst \
	Hacl.Spec.Poly1305_32.State.fst \
	Hacl.Spec.Poly1305_32.Lemmas.fst \
	Hacl.Spec.Poly1305_32.fst \
	Hacl.Spe.Poly1305_32.fst \
	Hacl.Bignum.Modulo.fst \
	Hacl.Bignum.AddAndMultiply.fst \
	Hacl.Impl.Poly1305_32.State.fst \
	Hacl.Impl.Poly1305_32.fst \
	Hacl.Standalone.Poly1305_32.fst \
	Hacl.Poly1305_32.fst

SLOW=

TODO=

POLY1305_FILES=$(BIGNUM) $(POLY1305_SPECIFIC)

FSTAR_INCLUDES+=--include $(HACL_HOME)/code/bignum

# Parameter for interactive mode
%.fst-in:
	@echo $(OPTIONS) --hint_info \
	$(FSTAR_INCLUDES)


ct: $(addsuffix -lax, $(POLY1305_FILES))
	# Using the --verify_all argument to lift abstractions, typechecks all dependencies of Curve25519.fst
	$(FSTAR) --lax --verify_all Hacl.Poly1305_32.fst

bignum-ver: $(addsuffix -reloc-verify, $(BIGNUM))
specific-ver: $(addsuffix -verify, $(POLY1305_SPECIFIC))
verify: bignum-ver specific-ver
all-ver: verify
all-ct: ct

# Hints regeneration
bignum-hints: $(addsuffix .reloc.hints, $(BIGNUM))
specific-hints: $(addsuffix .hints, $(POLY1305_SPECIFIC))
hints: bignum-hints specific-hints
all-hints: hints

# For CI, all modules restricted from incomplete or slow ones
bignum-ci: $(addsuffix -reloc-verify, $(filter-out $(SLOW) $(TODO), $(BIGNUM)))
specific-ci: $(addsuffix -verify, $(filter-out $(SLOW) $(TODO), $(POLY1305_SPECIFIC)))
all-ci: bignum-ci specific-ci

# By default, KreMLin drops a bunch of spec-related module that are not meant to
# extract.
CFLAGS=-Wall -Wextra -Wno-unused-parameter -Wno-unused-variable
KREMLIN_ARGS+=-I ../bignum -tmpdir poly-c \
	-fparentheses \
	$(KREMLIN_TESTLIB)

poly-c/out.krml: $(POLY1305_FILES) Hacl.Test.Poly1305_32.fst
	$(KREMLIN) $(KREMLIN_ARGS) -skip-translation $^ -o $@

poly-c/Hacl_Poly1305_32.c: poly-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) $^ \
		-bundle 'Hacl.Poly1305_32=*' \
		-minimal -add-include '"kremlib.h"' -skip-compilation

poly1305.exe: poly-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) \
		-no-prefix Hacl.Test.Poly1305_32 \
		-bundle 'Hacl.Spec.*,Hacl.Spe.*' \
		-drop FStar,Prims,LowStar,C.Loops.Spec.Loops,Combinators \
		-drop Hacl.Endianness,Spec.*,Hacl.Bignum.Parameters,Hacl.Endianness,Hacl.Spec,Hacl.Spec.*,Hacl.Spe,Hacl.Spe.*,Hacl.Cast,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128,Seq.* \
		-bundle 'Hacl.Poly1305_32=*' \
		$^ -o $@
	./$@

extract-c: poly-c/Hacl_Poly1305_32.c

test: poly1305.exe

perf:
	$(GCC) $(GCC_OPTS) -I $(KREMLIN_HOME)/kremlib -I poly-c -I $(HACL_HOME)/other_providers/openssl/crypto/poly1305 -I $(HACL_HOME)/other_providers/tweetnacl -I $(HACL_HOME)/test -I $(HACL_HOME)/other_providers/openssl/crypto/include poly-c/Hacl_Poly1305_32.c test-poly32.c

clean:
	rm -rf *.exe *.exe.* *.out *~ poly-c *.krml
