# Change to local F* root directory
FSTAR_HOME=~/dev/old_fstar/FStar
FSTAR=$(FSTAR_HOME)/bin/fstar.exe
OPTIONS=--lax --codegen OCaml --use_native_int
OPTIONS_VER=

# F* standard library files
FSTAR_LIB=FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Set.fst seq.fsi FStar.Seq.Base.fst FStar.Seq.Properties.fst FStar.Seq.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Array.fst FStar.Ghost.fst

MATH_DIR=./math_interfaces
BIGNUM_DIR=./bignum_proof
CURVE_DIR=./curve_proof

# Mathematical specifications
MATH_FILES=$(addprefix $(MATH_DIR)/, definitions.fst field.fst curve.fst)

# Bignum library files (changes on parameters, modulo and inverse (crecip))
BIGNUM_DONNA_64_FILES=$(addprefix $(BIGNUM_DIR)/, axiomatic.fst intlib.fst lemmas.fst parameters.fsti parameters_25519_64.fst uint.fst bigint.fst eval.fst modulo_lemmas.fst modulo_p25519_64.fst fsum_lemmas.fst fsum.fst fsum_wide.fst fdifference_lemmas.fst fdifference.fst fscalar_lemmas.fst fscalar.fst fproduct_lemmas.fst fproduct.fst bignum_lemmas.fst bignum.fst) $(addprefix $(CURVE_DIR)/, crecip_25519.fst)
BIGNUM_C448_FILES=$(addprefix $(BIGNUM_DIR)/, axiomatic.fst intlib.fst lemmas.fst parameters.fsti parameters_448_64.fst uint.fst bigint.fst eval.fst modulo_lemmas.fst modulo_p448_64.fst fsum_lemmas.fst fsum.fst fsum_wide.fst fdifference_lemmas.fst fdifference.fst fscalar_lemmas.fst fscalar.fst fproduct_lemmas.fst fproduct.fst bignum_lemmas.fst bignum.fst) $(addprefix $(CURVE_DIR)/, crecip_448.fst)
BIGNUM_P256_FILES=$(addprefix $(BIGNUM_DIR)/, axiomatic.fst intlib.fst lemmas.fst parameters.fsti parameters_256_64.fst uint.fst bigint.fst eval.fst modulo_256_64.fst fsum_lemmas.fst fsum.fst fsum_wide.fst fdifference_lemmas.fst fdifference.fst fscalar_lemmas.fst fscalar.fst fproduct_lemmas.fst fproduct.fst bignum_lemmas.fst bignum.fst) $(addprefix $(CURVE_DIR)/, crecip_256.fst)

# Curve files (changes on adding and doubling: one contains projective equations, the other jacobians 
CURVE_FILES=$(addprefix $(CURVE_DIR)/, concrete_point.fst double_and_add.fst montgomery_ladder_lemmas.fst montgomery_ladder.fst)
CURVE_FILES2=$(addprefix $(CURVE_DIR)/, concrete_point.fst double_and_add2.fst montgomery_ladder_lemmas.fst montgomery_ladder.fst)

# Output directories
C25519_64_ODIR=./c25519_64
C25519_64_OPTIONS=--odir $(C25519_64_ODIR) 
C448_64_ODIR=./c448_64
C448_64_OPTIONS=--odir $(C448_64_ODIR)
P256_ODIR=./p256
P256_OPTIONS=--odir $(P256_ODIR)

# OCaml files obtained after extraction (same module names for all curves)
CURVE_OCAML=$(addprefix $(FSTAR_HOME)/lib/ml/, native_int/prims.ml FStar_Set.ml FStar_ST.ml FStar_All.ml) FStar_FunctionalExtensionality.ml FStar_Seq.ml Parameters.ml IntLib.ml UInt.mli UInt.ml Bigint.mli Bigint.ml Eval.ml Modulo.ml Fsum.ml FsumWide.ml Fdifference.ml Fscalar.ml Fproduct.ml Bignum.ml ConcretePoint.ml DoubleAndAdd.ml MontgomeryLadder.ml 

# OCaml build variables
OCAML=ocamlfind ocamlopt -package batteries -package stdint -linkpkg -g -thread -O3 -w -20-26-11
DEBUG=ocamlfind ocamlc -package batteries -package stdint -linkpkg -g -thread
OCAML_INCLUDE_PATHS=$(addprefix -I , $(FSTAR_HOME)/lib/ml/native_int $(FSTAR_HOME)/lib/ml)

.PHONY:extract25519 extract448 extract_p256

all: curve25519 curve448 p256

# Compilation targets
curve25519: extract25519 test25519
curve448: extract448 test448
p256: extract_p256 test_p256

extract25519:
	@echo
	@echo "#######################################################"
	@echo "#               Extracting CURVE25519                 #"
	@echo "#######################################################"
	@echo
	mkdir -p $(C25519_64_ODIR)
	$(FSTAR) $(OPTIONS) $(C25519_64_OPTIONS) $(FSTAR_LIB) $(MATH_FILES) $(BIGNUM_DONNA_64_FILES) $(CURVE_FILES)
	@sed -i 's/let rec small_step = (Obj.magic /let rec small_step = (/g' $(C25519_64_ODIR)/MontgomeryLadder.ml # Corrects an extraction issue of F*
# Modules the code is compiled with
	@cp $(BIGNUM_DIR)/ml/IntLib.ml $(C25519_64_ODIR)/
	@cp $(BIGNUM_DIR)/ml/Bigint64.ml $(C25519_64_ODIR)/Bigint.ml
	@cp $(BIGNUM_DIR)/ml/Bigint64.mli $(C25519_64_ODIR)/Bigint.mli
	@cp $(BIGNUM_DIR)/ml/UInt64.ml $(C25519_64_ODIR)/UInt.ml
	@cp $(BIGNUM_DIR)/ml/UInt64.mli $(C25519_64_ODIR)/UInt.mli

extract448:
	@echo
	@echo "#######################################################"
	@echo "#               Extracting CURVE448                   #"
	@echo "#######################################################"
	@echo
	mkdir -p $(C448_64_ODIR)
	$(FSTAR) $(OPTIONS) $(C448_64_OPTIONS) $(FSTAR_LIB) $(MATH_FILES) $(BIGNUM_C448_FILES) $(CURVE_FILES)
	@sed -i 's/let rec small_step = (Obj.magic /let rec small_step = (/g' $(C448_64_ODIR)/MontgomeryLadder.ml # Corrects an extraction issue of F*
# Modules the code is compiled with
	@cp $(BIGNUM_DIR)/ml/IntLib.ml $(C448_64_ODIR)/
	@cp $(BIGNUM_DIR)/ml/Bigint64.ml $(C448_64_ODIR)/Bigint.ml
	@cp $(BIGNUM_DIR)/ml/Bigint64.mli $(C448_64_ODIR)/Bigint.mli
	@cp $(BIGNUM_DIR)/ml/UInt64.ml $(C448_64_ODIR)/UInt.ml
	@cp $(BIGNUM_DIR)/ml/UInt64.mli $(C448_64_ODIR)/UInt.mli

extract_p256:
	@echo
	@echo "#######################################################"
	@echo "#               Extracting NIST-P256                  #"
	@echo "#######################################################"
	@echo
	mkdir -p $(P256_ODIR)
	$(FSTAR) $(OPTIONS) $(P256_OPTIONS) $(FSTAR_LIB) $(MATH_FILES) $(BIGNUM_P256_FILES) $(CURVE_FILES2)
	@sed -i 's/let rec small_step = (Obj.magic /let rec small_step = (/g' $(P256_ODIR)/MontgomeryLadder.ml # Corrects an extraction issue of F*
# Modules the code is compiled with
	@cp $(BIGNUM_DIR)/ml/IntLib.ml $(P256_ODIR)/
	@cp $(BIGNUM_DIR)/ml/Bigint64.ml $(P256_ODIR)/Bigint.ml
	@cp $(BIGNUM_DIR)/ml/Bigint64.mli $(P256_ODIR)/Bigint.mli
	@cp $(BIGNUM_DIR)/ml/UInt64.ml $(P256_ODIR)/UInt.ml
	@cp $(BIGNUM_DIR)/ml/UInt64.mli $(P256_ODIR)/UInt.mli

# Cleaning target
clean:
	make -C bignum_proof clean
	make -C curve_proof clean
	rm -rf $(C25519_64_ODIR) $(C448_64_ODIR) $(P256_ODIR) *.out

# Test targets
test25519:
	@echo
	@echo "#######################################################"
	@echo "#               Compiling CURVE25519                  #"
	@echo "#######################################################"
	@echo
	cp $(CURVE_DIR)/ml/test_donna_64.ml $(C25519_64_ODIR)/test.ml
	cd $(C25519_64_ODIR) && $(OCAML) $(OCAML_INCLUDE_PATHS) $(CURVE_OCAML) Crecip.ml test.ml
	@echo
	@echo "#######################################################"
	@echo "#                 Testing CURVE25519                  #"
	@echo "#######################################################"
	@echo
	./$(C25519_64_ODIR)/a.out

test448:
	@echo
	@echo "#######################################################"
	@echo "#               Compiling CURVE448                  #"
	@echo "#######################################################"
	@echo
	cp $(CURVE_DIR)/ml/test_c448_64.ml $(C448_64_ODIR)/test.ml
	cd $(C448_64_ODIR) && $(OCAML) $(OCAML_INCLUDE_PATHS) $(CURVE_OCAML) Crecip.ml test.ml
	@echo
	@echo "#######################################################"
	@echo "#                 Testing CURVE448                    #"
	@echo "#######################################################"
	@echo
	./$(C448_64_ODIR)/a.out

test_p256:
	@echo
	@echo "#######################################################"
	@echo "#               Compiling NIST-P256                   #"
	@echo "#######################################################"
	@echo
	cp $(CURVE_DIR)/ml/test_p256.ml $(P256_ODIR)/test.ml
	cd $(P256_ODIR) && $(OCAML) $(OCAML_INCLUDE_PATHS) $(CURVE_OCAML) Crecip.ml test.ml
	@echo
	@echo "#######################################################"
	@echo "#                 Testing NIST-P256                   #"
	@echo "#######################################################"
	@echo
	./$(P256_ODIR)/a.out

fixlib:
	cp ./fstar_lib/FStar_ST.ml $(FSTAR_HOME)/lib/ml
