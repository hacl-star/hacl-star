CURVE_DIR=../curve_proof

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
CURVE_OCAML=$(addprefix ../old_fstar_lib/, prims.ml FStar_Set.ml FStar_ST.ml FStar_All.ml) FStar_FunctionalExtensionality.ml FStar_Seq.ml Parameters.ml IntLib.ml UInt.mli UInt.ml Bigint.mli Bigint.ml Eval.ml Modulo.ml Fsum.ml FsumWide.ml Fdifference.ml Fscalar.ml Fproduct.ml Bignum.ml ConcretePoint.ml DoubleAndAdd.ml MontgomeryLadder.ml 

# OCaml build variables
OCAML=ocamlfind ocamlopt -package batteries -package stdint -linkpkg -g -thread -O3 -w -20-26-11
DEBUG=ocamlfind ocamlc -package batteries -package stdint -linkpkg -g -thread
OCAML_INCLUDE_PATHS=$(addprefix -I , ../old_fstar_lib)

.PHONY:extract25519 extract448 extract_p256

all: curve25519 curve448 p256

# Compilation targets
curve25519: test25519
curve448: test448
p256: test_p256

# Cleaning target
clean:
	rm -rf $(addprefix $(C25519_64_ODIR)/, *.o *.cmi *.cmx *.out test.ml) \
		$(addprefix $(C448_64_ODIR)/, *.o *.cmi *.cmx *.out test.ml) \
		$(addprefix $(P256_ODIR)/, *.o *.cmi *.cmx *.out test.ml) \
		$(addprefix old_fstar_lib/, *.o *.cmi *.cmx) 

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
