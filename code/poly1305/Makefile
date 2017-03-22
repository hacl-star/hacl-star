FSTAR_HOME?=../../../dependencies/FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
HACL_HOME?=../..
include ../Makefile.include

SPECS=../../specs

INCLUDE_DIRS=../bignum ../lib/kremlin $(SPECS)


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

FSTARB=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
	$(addprefix --include , $(INCLUDE_DIRS)) --include $(KREMLIN_HOME)/kremlib

FSTAR_CT=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib --include ../bignum $(addprefix --include , $(SPECS)) \
		--include $(KREMLIN_HOME)/kremlib

# Lax typechecking against the restricted integer interface
%.fst-ct: %.fst
	$(FSTAR_CT) --lax $^

all-ct: $(addsuffix -ct, $(POLY1305_FILES))

# Full typechecking against the transparent integer interface
%.fst-verify: %.fst
	$(FSTARB) $^ --use_hints --record_hints

all-ver: $(addsuffix -verify, $(POLY1305_FILES))

# Minimal lax typechecking, pre-requisite to any extraction
%.fst-lax: %.fst
	$(FSTARB) --lax $^

all-lax: $(addsuffix -lax, $(POLY1305_FILES))

# Hints regeneration
%.fst-hints: %.fst
	-$(FSTARB) $^ --use_hints --record_hints

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
all-ci2: $(addsuffix -ci, $(filter-out $(SLOW) $(TODO), $(POLY1305_FILES)))
all-ci:
	cp bignum_hints/* ../bignum
	$(MAKE) all-ci2
	mv ../bignum/*.hints ./bignum_hints
bignum-ci:
	cp bignum_hints/* ../bignum
	$(MAKE) $(addsuffix -ci, $(BIGNUM))
	mv ../bignum/*.hints ./bignum_hints
specific-ci: $(addsuffix -ci, $(POLY1305_SPECIFIC))


test-c:
	# Weird \* because of https://caml.inria.fr/mantis/view.php?id=7473
	mkdir -p poly-c
	$(KREMLIN_HOME)/krml -tmpdir poly-c $(KREMLIN_ARGS) \
		$(addprefix -I , $(INCLUDE_DIRS)) \
		Poly1305_64.fst Hacl.Test.Poly1305_64.fst \
		-drop 'Combinators' -drop 'Hacl.Endianness' -drop 'Spec.\*' \
		-bundle 'Hacl.Spec.\*' -bundle 'Hacl.Spe.\*' \
		-drop 'Hacl.Bignum.Parameters' -drop 'Hacl.Endianness' \
		-drop 'Hacl.Spec' -drop 'Hacl.Spe' -drop 'Hacl.Cast' \
		-drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
		-drop Prims -drop FStar -bundle 'Poly1305_64=Hacl.Bignum.\*,Hacl.Impl.\*,Hacl.Standalone.\*,Poly1305_64,Hacl.Spec.\*,Hacl.Spe.\*' \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' \
                -no-prefix Hacl.Test.Poly1305_64 -o poly1305.exe
	./poly1305.exe

extract-c:
	# Weird \* because of https://caml.inria.fr/mantis/view.php?id=7473
	mkdir -p poly-c
	$(KREMLIN_HOME)/krml -tmpdir poly-c $(KREMLIN_ARGS) \
		$(addprefix -I , $(INCLUDE_DIRS)) \
		Poly1305_64.fst \
		-drop 'Combinators' -drop 'Hacl.Endianness' -drop 'Spec.\*' \
		-bundle 'Hacl.Spec.\*' -bundle 'Hacl.Spe.\*' \
		-drop 'Hacl.Bignum.Parameters' -drop 'Hacl.Endianness' \
		-drop 'Hacl.Spec' -drop 'Hacl.Spe' -drop 'Hacl.Cast' \
		-drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
		-drop Prims -drop FStar -bundle 'Poly1305_64=Hacl.Bignum.\*,Hacl.Impl.\*,Hacl.Standalone.\*,Poly1305_64,Hacl.Spec.\*,Hacl.Spe.\*' \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' \
                -skip-linking


include $(FSTAR_HOME)/src/gmake/fstar.mk
include $(FSTAR_HOME)/ulib/ml/Makefile.include
CODEGEN_ARGS=--lax --codegen OCaml --no_location_info $(FSTAR_DEFAULT_ARGS)
OCAMLOPT := $(OCAMLOPT) -w -8-20-26-28-10
POLY_EXTRACTED=Hacl_Bignum_Constants.ml Hacl_Bignum_Parameters.ml Hacl_MAC_Poly1305_64.ml

extract-ml:
	mkdir -p poly-ml
	$(FSTAR) $(CODEGEN_ARGS) --include $(FSTAR_HOME)/ulib/hyperstack --include ../bignum --include ../lib \
	--odir poly-ml $(POLY1305_FILES) \
	--no_extract FStar.Math.Lib --no_extract FStar.HyperHeap --no_extract FStar.HyperStack --no_extract FStar.ST --no_extract FStar.Seq --no_extract FStar.UInt128 --no_extract FStar.Int128  --no_extract FStar.Int64 --no_extract FStar.UInt63 --no_extract FStar.Int63 --no_extract FStar.UInt32 --no_extract FStar.Int32 --no_extract FStar.UInt31 --no_extract FStar.Int31 --no_extract FStar.UInt16 --no_extract FStar.Int16 --no_extract FStar.UInt8 --no_extract FStar.Int8 --no_extract Hacl.UInt64 --no_extract Hacl.UInt32 --no_extract Hacl.UInt128 --no_extract Hacl.UInt16 --trace_error 
	$(OCAMLOPT) -I poly-ml  -I ../lib/ml -I $(FSTAR_HOME)/ulib/ml/hyperstack -I $(FSTAR_HOME)/ulib/ml $(addprefix poly-ml/,$(POLY_EXTRACTED)) 

compile-ml:
	$(OCAMLOPT) -I poly-ml -I ../lib/ml -I $(FSTAR_HOME)/ulib/ml/hyperstack -I $(FSTAR_HOME)/ulib/ml $(addprefix poly-ml/,$(POLY_EXTRACTED)) 

clean:
	rm -rf *.exe *.exe.* *.out *~ poly-c
