# Define the location of F*'s main directory
FSTAR_HOME=~/dev/old_fstar/FStar
FSTAR=$(FSTAR_HOME)/bin/fstar.exe
OPTIONS=--lax --admit_fsi FStar.Set --codegen OCaml --use_native_int

# F*'s native libraries
FSTAR_LIB=FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi seq.fsi FStar.Seq.Base.fst FStar.Seq.Properties.fst FStar.Seq.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Array.fst FStar.Ghost.fst

# Field and Curve specifications
MATH=$(addprefix ../math_interfaces/, definitions.fst field.fst curve.fst)

CURVE_DONNA64=axiomatic.fst intlib.fst lemmas.fst parameters.fsti parameters_25519_64.fst uint.fst bigint.fst eval.fst
CURVE_448=axiomatic.fst intlib.fst lemmas.fst parameters.fsti parameters_448_64.fst uint.fst bigint.fst eval.fst
CURVE_P256=axiomatic.fst intlib.fst lemmas.fst parameters.fsti parameters_256_64.fst uint.fst bigint.fst eval.fst
BIGNUM=fsum_lemmas.fst fsum.fst fsum_wide.fst fdifference_lemmas.fst fdifference.fst fscalar_lemmas.fst fscalar.fst fproduct_lemmas.fst fproduct.fst bignum_lemmas.fst bignum.fst

# Output directories
C25519_64_ODIR=./c25519_64
C25519_64_OPTIONS=--odir $(C25519_64_ODIR)
C448_64_ODIR=./c448_64
C448_64_OPTIONS=--odir $(C448_64_ODIR)
P256_ODIR=./p256
P256_OPTIONS=--odir $(P256_ODIR)

# OCaml build variables
CURVE_OCAML=$(addprefix $(FSTAR_HOME)/lib/ml/, native_int/prims.ml FStar_Set.ml FStar_ST.ml FStar_All.ml) FStar_FunctionalExtensionality.ml FStar_Seq.ml Parameters.ml IntLib.ml UInt.mli UInt.ml Bigint.ml Eval.ml Modulo.ml Fsum.ml FsumWide.ml Fdifference.ml Fscalar.ml Fproduct.ml Bignum.ml
OCAML=ocamlfind ocamlopt -package batteries -package stdint -linkpkg -g -thread
DEBUG=ocamlfind ocamlc -package batteries -package stdint -linkpkg -g -thread
OCAML_INCLUDE_PATHS=$(addprefix -I , $(FSTAR_HOME)/lib/ml/native_int $(FSTAR_HOME)/lib/ml)

.PHONY: uint.fst

all:lemmas bigint eval fsum fsum_wide fdifference fscalar fproduct modulo_25519 bignum

# Common verification options
VER_OPTIONS=--admit_fsi FStar.Set --admit_fsi Parameters $(FSTAR_LIB)

# 40s on a i7 Haskwell laptop
lemmas: axiomatic.fst intlib.fst lemmas.fst fsum_lemmas.fst fdifference_lemmas.fst fscalar_lemmas.fst fproduct_lemmas.fst
	$(FSTAR) --z3timeout 10 $(VER_OPTIONS) $^ --verify_module Axiomatic --verify_module IntLib --verify_module Lemmas --verify_module FsumLemmas --verify_module FdifferenceLemmas --verify_module FproductLemmas --verify_module FscalarLemmas

# 4s on a i7 Haskwell laptop
uint.fst:
	$(FSTAR) --z3timeout 5 $(VER_OPTIONS) axiomatic.fst intlib.fst lemmas.fst parameters.fsti uint.fst --verify_module UInt

# 14s on a i7 Haskwell laptop
bigint: bigint.fst
	$(FSTAR) --z3timeout 20 $(VER_OPTIONS) axiomatic.fst intlib.fst lemmas.fst parameters.fsti uint.fst bigint.fst --verify_module Bigint

# 8s on a i7 Haskwell laptop
eval: eval.fst
	$(FSTAR) --z3timeout 150 $(VER_OPTIONS) axiomatic.fst intlib.fst lemmas.fst parameters.fsti uint.fst bigint.fst eval.fst --verify_module Eval

# 13s on a i7 Haskwell laptop
fsum: fsum_lemmas.fst fsum.fst
	$(FSTAR) --z3timeout 100 $(VER_OPTIONS) axiomatic.fst intlib.fst lemmas.fst parameters.fsti uint.fst bigint.fst eval.fst $^ --verify_module Fsum

# 21min on a i7 Haskwell laptop
fsum_wide: fsum_lemmas.fst fsum_wide.fst
	$(FSTAR) --z3timeout 500 $(VER_OPTIONS) axiomatic.fst intlib.fst lemmas.fst parameters.fsti uint.fst bigint.fst eval.fst $^ --verify_module FsumWide

# 6min on a i7 Haskwell laptop
fdifference: fdifference_lemmas.fst fdifference.fst
	$(FSTAR) --z3timeout 100 $(VER_OPTIONS) axiomatic.fst intlib.fst lemmas.fst parameters.fsti uint.fst bigint.fst eval.fst $^ --verify_module Fdifference

# 16s on a i7 Haskwell laptop
fscalar: fscalar_lemmas.fst fscalar.fst
	$(FSTAR) --z3timeout 300 $(VER_OPTIONS) axiomatic.fst intlib.fst lemmas.fst parameters.fsti uint.fst bigint.fst eval.fst $^ --verify_module Fscalar

# 33min on a i7 Haskwell laptop
fproduct: fproduct_lemmas.fst fproduct.fst
	$(FSTAR) --z3timeout 1000 $(VER_OPTIONS) --admit_fsi Fsum --admit_fsi FsumWide --admit_fsi Fscalar axiomatic.fst intlib.fst lemmas.fst parameters.fsti uint.fst bigint.fst eval.fst fsum.fsti fsum_wide.fsti fscalar.fsti $^ --verify_module Fproduct

# 78min on a i7 Haskwell laptop
modulo_25519: modulo_lemmas.fst modulo.fsti modulo_p25519_64.fst
	$(FSTAR) --z3timeout 500 $(FSTAR_LIB) --admit_fsi FStar.Set axiomatic.fst intlib.fst lemmas.fst parameters_25519_64.fst uint.fst bigint.fst eval.fst $^ --verify_module ModuloLemmas --verify_module Modulo

#
modulo_448: modulo_lemmas.fst modulo.fsti modulo_p448_64.fst
	$(FSTAR) --z3timeout 500 $(FSTAR_LIB) --admit_fsi FStar.Set axiomatic.fst intlib.fst lemmas.fst parameters_448_64.fst uint.fst bigint.fst eval.fst $^ --verify_module Modulo

#
modulo_256: modulo_lemmas.fst modulo.fsti modulo_256_64.fst
	$(FSTAR) --z3timeout 2000 $(FSTAR_LIB) --admit_fsi FStar.Set axiomatic.fst intlib.fst lemmas.fst parameters_256_64.fst uint.fst bigint.fst eval.fst $^ --verify_module Modulo

# 
bignum: bignum.fst
	$(FSTAR) --z3timeout 4000 $(VER_OPTIONS) --admit_fsi Modulo axiomatic.fst intlib.fst lemmas.fst parameters.fsti ../math_interfaces/definitions.fst ../math_interfaces/field.fst uint.fst bigint.fst eval.fst modulo.fsti fsum_lemmas.fst fsum.fst fsum_wide.fst fdifference_lemmas.fst fdifference.fst fscalar_lemmas.fst fscalar.fst fproduct_lemmas.fst fproduct.fst bignum_lemmas.fst $^ --verify_module Bignum
#
# Extraction and compilation targets
#
extract_25519_64:
	mkdir -p $(C25519_64_ODIR)
	$(FSTAR) $(OPTIONS) $(C25519_64_OPTIONS) $(FSTAR_LIB) $(MATH) $(CURVE_DONNA64) modulo_lemmas.fst modulo_p25519_64.fst $(BIGNUM)
	@cp ./ml/IntLib.ml $(C25519_64_ODIR)/
	@cp ./ml/Bigint64.ml $(C25519_64_ODIR)/Bigint.ml
	@cp ./ml/UInt64.ml $(C25519_64_ODIR)/UInt.ml
	@cp ./ml/UInt64.mli $(C448_64_ODIR)/UInt.mli

extract_448_64:
	mkdir -p $(C448_64_ODIR)
	$(FSTAR) $(OPTIONS) $(C448_64_OPTIONS) $(FSTAR_LIB) $(MATH) $(CURVE_448) modulo_lemmas.fst  modulo_p448_64.fst $(BIGNUM)
	@cp ./ml/IntLib.ml $(C448_64_ODIR)/
	@cp ./ml/Bigint64.ml $(C448_64_ODIR)/Bigint.ml
	@cp ./ml/UInt64.ml $(C448_64_ODIR)/UInt.ml
	@cp ./ml/UInt64.mli $(C448_64_ODIR)/UInt.mli

extract_p256:
	mkdir -p $(P256_ODIR)
	$(FSTAR) $(OPTIONS) $(P256_OPTIONS) $(FSTAR_LIB) $(MATH) $(CURVE_P256) modulo_256_64.fst $(BIGNUM)
	@cp ./ml/IntLib.ml $(P256_ODIR)/
	@cp ./ml/Bigint64.ml $(P256_ODIR)/Bigint.ml
	@cp ./ml/UInt64.ml $(P256_ODIR)/UInt.ml
	@cp ./ml/UInt64.mli $(C448_64_ODIR)/UInt.mli

test_25519_64:
	cp ./ml/test_donna_64.ml $(C25519_64_ODIR)/test.ml
	cd $(C25519_64_ODIR) && $(DEBUG) $(OCAML_INCLUDE_PATHS) $(CURVE_OCAML) test.ml
	./$(C25519_64_ODIR)/a.out

test_448_64:
	cp ./ml/test_c448_64.ml $(C448_64_ODIR)/test.ml
	cd $(C448_64_ODIR) && $(DEBUG) $(OCAML_INCLUDE_PATHS) $(CURVE_OCAML) test.ml
	./$(C448_64_ODIR)/a.out

test_p256:
	cp ./ml/test_p256.ml $(P256_ODIR)/test.ml
	cd $(P256_ODIR) && $(DEBUG) $(OCAML_INCLUDE_PATHS) $(CURVE_OCAML) test.ml
	./$(P256_ODIR)/a.out

clean:
	rm -rf ./c25519_64 ./c25519 ./c448_64
	cd ./ml && rm -rf *.cm* *.o *~
