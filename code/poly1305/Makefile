include ../Makefile.include

BIGNUM= \
	../bignum/Hacl.Spec.Bignum.Field.fst \
	../bignum/Hacl.Bignum.Limb.fst \
	../bignum/Hacl.Bignum.Wide.fst \
	../bignum/Hacl.Spec.Bignum.Bigint.fst \
	../bignum/Hacl.Spec.Bignum.Fsum.fst \
	../bignum/Hacl.Spec.Bignum.Fproduct.fst \
	../bignum/Hacl.Spec.Bignum.Fmul.fst \
	../bignum/Hacl.Bignum.Fsum.fst \
	../bignum/Hacl.Bignum.Fproduct.fst \
	../bignum/Hacl.Bignum.Fmul.fst \


POLY1305_SPECIFIC= \
	Hacl.Bignum.Constants.fst \
	Hacl.Bignum.Parameters.fst \
	Hacl.Spec.Bignum.Modulo.fst \
	Hacl.Spec.Bignum.AddAndMultiply.fst \
	../../specs/Spec.Poly1305.fst \
	Hacl.Spec.Poly1305_64.fst \
	Hacl.Spe.Poly1305_64.fst \
	Hacl.Bignum.Modulo.fst \
	Hacl.Bignum.AddAndMultiply.fst \
	Hacl.Impl.Poly1305_64.fst \
	Hacl.Standalone.Poly1305_64.fst \
	Poly1305_64.fst \
	Hacl.Spec.Poly1305_64.Lemmas1.fst \
	AEAD.Poly1305_64.fst

SLOW=

TODO=

POLY1305_FILES=$(BIGNUM) $(POLY1305_SPECIFIC)

FSTAR_INCLUDES+=--include ../bignum

ct: $(addsuffix -lax, $(POLY1305_FILES))
	# Using the --verify_all argument to lift abstractions, typechecks all dependencies of Curve25519.fst
	$(FSTAR) --lax --verify_all Poly1305_64.fst

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
	-bundle 'Hacl.Spec.\*,Hacl.Spe.\*' -fparentheses \
	-drop Combinators,Hacl.Endianness,Spec.*,Hacl.Bignum.Parameters,Hacl.Endianness,Hacl.Spec,Hacl.Spe,Hacl.Cast,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128,Prims,FStar,Seq.* \
	$(KREMLIN_TESTLIB)
CFLAGS+= 

# Acknowledge the F* dependency graph
.PHONY: depend
depend:
	$(FSTAR) --dep make $(POLY1305_FILES) > .depend
-include .depend

# The F* -> out.krml step only depends on F* files.
poly-c/out.krml: $(POLY1305_FILES) Hacl.Test.Poly1305_64.fst
	$(KREMLIN) $(KREMLIN_ARGS) -skip-translation $^

# We need one invocation of kremlin for each bundle because of KreMLin bug #43
poly-c/Poly1305_64.c poly-c/Hacl_Test_Poly1305_64.c: poly-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -skip-compilation $^ \
		-drop AEAD_Poly1305_64 -no-prefix Hacl.Test.Poly1305_64 \
		-bundle 'Poly1305_64=Hacl.Bignum.\*,Hacl.Impl.\*,Hacl.Standalone.\*,Poly1305_64'

poly-c/AEAD_Poly1305_64.c: poly-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -skip-compilation $^ \
		-drop Poly1305_64,Hacl.Test.Poly1305_64 \
		-bundle 'AEAD.Poly1305_64=Hacl.Bignum.\*,Hacl.Impl.\*,Hacl.Standalone.\*,AEAD.Poly1305_64,Poly1305_64,Hacl.Spec.\*'

poly1305.exe: $(POLY1305_FILES) Hacl.Test.Poly1305_64.fst
	$(KREMLIN) $(KREMLIN_ARGS) \
		-drop AEAD_Poly1305_64 -no-prefix Hacl.Test.Poly1305_64 \
		-bundle 'Poly1305_64=Hacl.Bignum.\*,Hacl.Impl.\*,Hacl.Standalone.\*,Poly1305_64' \
		$^ -o $@
	./$@

extract-c: poly-c/Poly1305_64.c # poly-c/AEAD_Poly1305_64.c

test: poly1305.exe


include $(FSTAR_HOME)/ulib/ml/Makefile.include
CODEGEN_ARGS=--lax --codegen OCaml --no_location_info $(FSTAR_DEFAULT_ARGS)
OCAMLOPT := $(OCAMLOPT) -w -8-20-26-28-10
POLY_EXTRACTED=Hacl_Bignum_Constants.ml Hacl_Bignum_Parameters.ml Hacl_MAC_Poly1305_64.ml

extract-ml:
	mkdir -p poly-ml
	$(FSTAR) $(CODEGEN_ARGS) --include ../bignum --include ../lib \
	--odir poly-ml $(POLY1305_FILES) \
	 --no_extract Hacl.UInt64 --no_extract Hacl.UInt32 --no_extract Hacl.UInt128 --no_extract Hacl.UInt16 --trace_error
	$(OCAMLOPT) -I poly-ml  -I ../lib/ml -I $(FSTAR_HOME)/ulib/ml $(addprefix poly-ml/,$(POLY_EXTRACTED))

compile-ml:
	$(OCAMLOPT) -I poly-ml -I ../lib/ml -I $(FSTAR_HOME)/ulib/ml $(addprefix poly-ml/,$(POLY_EXTRACTED))

count-line:
	cloc --force-lang=ocaml $(POLY1305_SPECIFIC)

clean:
	rm -rf *.exe *.exe.* *.out *~ poly-c
