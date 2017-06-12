include ../Makefile.include

SPECS=../../specs

INCLUDE_DIRS=../bignum ../lib/kremlin $(KREMLIN_HOME)/kremlib $(SPECS)


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

POLY1305_FILES= $(BIGNUM) $(POLY1305_SPECIFIC)

FSTARB=$(FSTAR_BASE) \
	$(addprefix --include , $(INCLUDE_DIRS)) --include $(KREMLIN_HOME)/kremlib	

FSTAR_CT=$(FSTAR_BASE) \
	--include ../lib --include ../bignum $(addprefix --include , $(SPECS)) \
	--include $(KREMLIN_HOME)/kremlib

# Lax typechecking against the restricted integer interface
%.fst-ct: %.fst
	$(FSTAR_CT) --lax $^

# Using the --verify_all argument to lift abstractions, typechecks all dependencies of Curve25519.fst
all-ct:
	$(FSTAR_CT) --lax --verify_all Poly1305_64.fst

# Full typechecking against the transparent integer interface
%.fst-verify: %.fst
	$(FSTARB) $^
%.fsti-verify: %.fsti
	$(FSTARB) $^

all-ver: $(addsuffix -verify, $(POLY1305_FILES))

# Minimal lax typechecking, pre-requisite to any extraction
%.fst-lax: %.fst
	$(FSTARB) --lax $^

all-lax: $(addsuffix -lax, $(POLY1305_FILES))

# Hints regeneration
%.fst-hints: %.fst
	-$(FSTARB) --record_hints $^

all-hints2: $(addsuffix -hints, $(POLY1305_FILES))
all-hints:
	cp bignum_hints/* ../bignum
	$(MAKE) all-hints2
	mv ../bignum/*.hints ./bignum_hints
bignum-hints:
	cp bignum_hints/* ../bignum
	$(MAKE) $(addsuffix -hints, $(BIGNUM))
	mv ../bignum/*.hints ./bignum_hints
specific-hints: $(addsuffix -hints, $(POLY1305_SPECIFIC))

# For CI, all modules restricted from incomplete or slow ones
all-ci2: $(addsuffix -verify, $(filter-out $(SLOW) $(TODO), $(POLY1305_FILES)))
all-ci:
	cp bignum_hints/* ../bignum
	$(MAKE) all-ci2
	mv ../bignum/*.hints ./bignum_hints
bignum-ci:
	cp bignum_hints/* ../bignum
	$(MAKE) $(addsuffix -verify, $(filter-out $(SLOW) $(TODO), $(BIGNUM)))
	mv ../bignum/*.hints ./bignum_hints
specific-ci: $(addsuffix -verify, $(filter-out $(SLOW) $(TODO), $(POLY1305_SPECIFIC)))

# An exemplary Makefile for extraction that splits out the out.krml generation
# and the .c file generation, with proper dependencies on .fst files.

# By default, KreMLin drops a bunch of spec-related module that are not meant to
# extract.
INCLUDES=$(addprefix -I , $(INCLUDE_DIRS))
CFLAGS=-Wall -Wextra -Wno-unused-parameter -Wno-unused-variable
KRML_BIN=$(KREMLIN_HOME)/_build/src/Kremlin.native
KRML=$(KRML_BIN) $(KREMLIN_ARGS) $(INCLUDES) -tmpdir poly-c \
  -bundle 'Hacl.Spec.\*' -bundle 'Hacl.Spe.\*' -fparentheses \
  -add-include '"testlib.h"' \
  -drop Combinators,Hacl.Endianness,Spec.*,Hacl.Bignum.Parameters,Hacl.Endianness,Hacl.Spec,Hacl.Spe,Hacl.Cast,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128,Prims,FStar,Seq.*

# Acknowledge the F* dependency graph
.PHONY: depend
depend:
	$(FSTARB) --dep make $(POLY1305_FILES) > .depend
-include .depend

# The F* -> out.krml step only depends on F* files.
poly-c/out.krml: $(POLY1305_FILES) Hacl.Test.Poly1305_64.fst
	$(KRML) -skip-translation $^

# We need one invocation of kremlin for each bundle because of KreMLin bug #43
poly-c/Poly1305_64.c poly-c/Hacl_Test_Poly1305_64.c: poly-c/out.krml $(KRML_BIN)
	$(KRML) -skip-compilation $< \
	  -drop AEAD_Poly1305_64 \
	  -no-prefix Hacl.Test.Poly1305_64 \
	  -bundle 'Poly1305_64=Hacl.Bignum.\*,Hacl.Impl.\*,Hacl.Standalone.\*,Poly1305_64'

poly-c/AEAD_Poly1305_64.c: poly-c/out.krml $(KRML_BIN)
	$(KRML) -skip-compilation $< \
	  -drop Poly1305_64,Hacl.Test.Poly1305_64 \
	  -bundle 'AEAD.Poly1305_64=Hacl.Bignum.\*,Hacl.Impl.\*,Hacl.Standalone.\*,AEAD.Poly1305_64,Poly1305_64,Hacl.Spec.\*'

poly1305.exe: poly-c/Poly1305_64.c poly-c/Hacl_Test_Poly1305_64.c $(KREMLIN_HOME)/kremlib/kremlib.c $(KREMLIN_HOME)/kremlib/testlib.c
	$(CC) $(INCLUDES) $(CFLAGS) $^ -o $@
	./$@

extract-c: poly-c/Poly1305_64.c poly-c/AEAD_Poly1305_64.c

include $(FSTAR_HOME)/src/gmake/fstar.mk
include $(FSTAR_HOME)/ulib/ml/Makefile.include
CODEGEN_ARGS=--lax --codegen OCaml --no_location_info $(FSTAR_DEFAULT_ARGS)
OCAMLOPT := $(OCAMLOPT) -w -8-20-26-28-10
POLY_EXTRACTED=Hacl_Bignum_Constants.ml Hacl_Bignum_Parameters.ml Hacl_MAC_Poly1305_64.ml

extract-ml:
	mkdir -p poly-ml
	$(FSTAR) $(CODEGEN_ARGS)  --include ../bignum --include ../lib \
	--odir poly-ml $(POLY1305_FILES) \
	--no_extract FStar.Math.Lib --no_extract FStar.HyperHeap --no_extract FStar.HyperStack --no_extract FStar.ST --no_extract FStar.Seq --no_extract FStar.UInt128 --no_extract FStar.Int128  --no_extract FStar.Int64 --no_extract FStar.UInt63 --no_extract FStar.Int63 --no_extract FStar.UInt32 --no_extract FStar.Int32 --no_extract FStar.UInt31 --no_extract FStar.Int31 --no_extract FStar.UInt16 --no_extract FStar.Int16 --no_extract FStar.UInt8 --no_extract FStar.Int8 --no_extract Hacl.UInt64 --no_extract Hacl.UInt32 --no_extract Hacl.UInt128 --no_extract Hacl.UInt16 --trace_error 
	$(OCAMLOPT) -I poly-ml  -I ../lib/ml  -I $(FSTAR_HOME)/ulib/ml $(addprefix poly-ml/,$(POLY_EXTRACTED)) 

compile-ml:
	$(OCAMLOPT) -I poly-ml -I ../lib/ml  -I $(FSTAR_HOME)/ulib/ml $(addprefix poly-ml/,$(POLY_EXTRACTED)) 

count-line:
	cloc --force-lang=ocaml $(POLY1305_SPECIFIC)

clean:
	rm -rf *.exe *.exe.* *.out *~ poly-c
