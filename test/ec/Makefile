# FStar variables
FSTAR_HOME?=../../../FStar
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_DEFAULT_ARGS) # from the included Makefile

LIB_DIR=../../lib/st
LIB_FILES=$(addprefix $(LIB_DIR)/, axioms.fst intlib.fst IntLibLemmas.fst sint.fst sbuffer.fst SInt.UInt8.fst SInt.UInt32.fst SInt.UInt63.fst SInt.UInt64.fst SInt.Cast.fst SBytes.fst)

LIB_DIR_HST=../../lib/hst
LIB_FILES_HST=$(addprefix $(LIB_DIR_HST)/, Math.Axioms.fst Math.Lib.fst Math.Lemmas.fst Hacl.UInt8.fst Hacl.UInt32.fst Hacl.UInt64.fst Hacl.UInt128.fst Hacl.SBuffer.fst Hacl.Cast.fst)

CODE_DIR=../../crypto/ec
CODE_DIR_HST=../../crypto_hst/ec

OPTIONS_OCAML=--lax --codegen OCaml --no_location_info --use_native_int
OPTIONS_OCAML_HST=--lax --codegen OCaml --no_location_info

# OCaml variables
OCAMLOPT := $(OCAMLOPT) -w -20-26-8-10-58
REALIZED_MLI=SInt_UInt8 SInt_UInt32 SInt_UInt63 SInt_UInt64
REALIZED=SInt_Cast SBuffer SBytes
REALIZED_MODULE=$(subst _,., $(REALIZED))
REALIZED_ML=$(addsuffix .mli,$(REALIZED_MLI)) $(addsuffix .ml,$(REALIZED_MLI) $(REALIZED))
NO_CODEGEN=$(addprefix --no_extract , SInt $(REALIZED_MODULE))

# OCaml HST variables
REALIZED_MLI_HST=Hacl_UInt8 Hacl_UInt32 Hacl_UInt64 Hacl_UInt128
REALIZED_HST=FStar_HyperStack FStar_HST Hacl_Cast Hacl_SBuffer 
REALIZED_MODULE_HST=$(subst _,., $(REALIZED_HST))
REALIZED_ML_HST=$(addsuffix .mli,$(REALIZED_MLI_HST)) $(addsuffix .ml,$(REALIZED_MLI_HST) $(REALIZED_HST))
NO_CODEGEN_HST=$(addprefix --no_extract , $(REALIZED_MODULE_HST))

# F* ST files
CURVE_25519_FSTAR=$(addprefix $(CODE_DIR)/,Bignum.Parameters.fst Bignum.Bigint.fst Bignum.Fsum.fst Bignum.FsumWide.fst Bignum.FdifferenceLemmas.fst Bignum.Fdifference.fst Bignum.Fscalar.fst Bignum.Fproduct.fst Bignum.Modulo.fst Bignum.Core.fst Curve.Point.fst Curve.AddAndDouble.fst Curve.Ladder.fst)

# F* HST files
CURVE_FSTAR_HST=$(addprefix $(CODE_DIR_HST)/, Math.Definitions.fst Math.Field.fst Math.Curve.fst Curve.Parameters.fst Curve.Bigint.fst Curve.Fsum.fst Curve.FsumWide.fst Curve.Fdifference.fst Curve.Fscalar.fst Curve.Fproduct.fst Curve.Modulo.fst Curve.Bignum.fst Curve.Crecip.fst Curve.Point.fst Curve.AddAndDouble.fst Curve.Ladder.fst)

# Extracted OCaml files
CURVE_EXTRACTED=FStar_FunctionalExtensionality.ml FStar_TSet.ml FStar_List_Tot.ml FStar_Seq.ml FStar_Ghost.ml Axioms.ml Bignum_Parameters.ml Bignum_Bigint.ml Bignum_Fsum.ml Bignum_FsumWide.ml Bignum_Fdifference.ml Bignum_Fscalar.ml Bignum_Fproduct.ml Bignum_Modulo.ml Bignum_Core.ml Curve_Point.ml Curve_AddAndDouble.ml Curve_Ladder.ml

# Extracted OCaml HST files
CURVE_EXTRACTED_HST=FStar_FunctionalExtensionality.ml FStar_TSet.ml FStar_List_Tot.ml FStar_Seq.ml FStar_Ghost.ml Math_Axioms.ml Math_Lib.ml Math_Lemmas.ml Math_Definitions.ml Math_Field.ml Math_Curve.ml Curve_Parameters.ml Curve_Bigint.ml Curve_Fsum.ml Curve_FsumWide.ml Curve_Fdifference.ml Curve_Fscalar.ml Curve_Fproduct.ml Curve_Modulo.ml Curve_Bignum.ml Curve_Crecip.ml Curve_Point.ml Curve_AddAndDouble.ml Curve_Ladder.ml

CURVE25519_FSTAR=$(CURVE_FSTAR_HST) $(CODE_DIR_HST)/Curve.Curve25519.fst
P256_FSTAR=$(CURVE_FSTAR_HST) $(CODE_DIR_HST)/Curve.P256.fst
CURVE448_FSTAR=$(CURVE_FSTAR_HST) $(CODE_DIR_HST)/Curve.Curve448.fst

CURVE25519_EXTRACTED=$(CURVE_EXTRACTED_HST) Curve_Curve25519.ml
P256_EXTRACTED=$(CURVE_EXTRACTED_HST) Curve_P256.ml
CURVE448_EXTRACTED=$(CURVE_EXTRACTED_HST) Curve_Curve448.ml

CURVE25519_ODIR=curve25519
CURVE448_ODIR=curve448
P256_ODIR=p256

.PHONY: curve-ml curve25519 curve448 p256

all: curve25519 curve448 #curve-ml

# Curve25519 extraction to OCaml
curve-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean all PRIMS_DIR=native_int
	mkdir -p $(CURVE25519_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(LIB_FILES) $(CURVE_25519_FSTAR) --odir $(CURVE25519_ODIR)
	@sed -i 's/(Obj.magic ((fun pp ppq p pq q n ctr b scalar/(((fun pp ppq p pq q n ctr b scalar/g' $(CURVE25519_ODIR)/Curve_Ladder.ml
	$(OCAMLOPT) -I $(ULIB_ML)/native_int -I $(LIB_DIR)/ml -I $(CURVE25519_ODIR) $(addprefix $(LIB_DIR)/ml/,$(REALIZED_ML)) \
	  $(addprefix $(CURVE25519_ODIR)/,$(CURVE_EXTRACTED)) ml/test_curve25519.ml -o test_curve25519.exe
	./test_curve25519.exe

# Curve25519 HST extraction to OCaml
curve25519:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean all
	@mkdir -p $(CURVE25519_ODIR)
	@cp $(CODE_DIR_HST)/curve_specific/Curve25519.Parameters.fst $(CODE_DIR_HST)/Curve.Parameters.fst
	@cp $(CODE_DIR_HST)/curve_specific/Curve25519.Modulo.fst $(CODE_DIR_HST)/Curve.Modulo.fst
	@cp $(CODE_DIR_HST)/curve_specific/Curve25519.Crecip.fst $(CODE_DIR_HST)/Curve.Crecip.fst
	@cp $(CODE_DIR_HST)/curve_specific/Curve.AddAndDoubleM.fst $(CODE_DIR_HST)/Curve.AddAndDouble.fst
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML_HST) $(LIB_FILES_HST) $(CURVE25519_FSTAR) --odir $(CURVE25519_ODIR)
	@rm $(addprefix $(CODE_DIR_HST)/Curve., Parameters.fst Modulo.fst Crecip.fst AddAndDouble.fst)
	@sed -i 's/(Obj.magic ((fun pp ppq p pq q n ctr b scalar/(((fun pp ppq p pq q n ctr b scalar/g' $(CURVE25519_ODIR)/Curve_Ladder.ml
	$(OCAMLOPT) -I $(LIB_DIR_HST)/ml -I $(CURVE25519_ODIR) $(addprefix $(LIB_DIR_HST)/ml/,$(REALIZED_ML_HST)) \
	  $(addprefix $(CURVE25519_ODIR)/,$(CURVE25519_EXTRACTED)) ml/test_curve25519_hst.ml -o test_curve25519.exe
	./test_curve25519.exe

# Curve448 HST extraction to OCaml
curve448:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean all
	@mkdir -p $(CURVE448_ODIR)
	@cp $(CODE_DIR_HST)/curve_specific/Curve448.Parameters.fst $(CODE_DIR_HST)/Curve.Parameters.fst
	@cp $(CODE_DIR_HST)/curve_specific/Curve448.Modulo.fst $(CODE_DIR_HST)/Curve.Modulo.fst
	@cp $(CODE_DIR_HST)/curve_specific/Curve448.Crecip.fst $(CODE_DIR_HST)/Curve.Crecip.fst
	@cp $(CODE_DIR_HST)/curve_specific/Curve.AddAndDoubleM.fst $(CODE_DIR_HST)/Curve.AddAndDouble.fst
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML_HST) $(LIB_FILES_HST) $(CURVE448_FSTAR) --odir $(CURVE448_ODIR)
	@rm $(addprefix $(CODE_DIR_HST)/Curve., Parameters.fst Modulo.fst Crecip.fst AddAndDouble.fst)
	@sed -i 's/(Obj.magic ((fun pp ppq p pq q n ctr b scalar/(((fun pp ppq p pq q n ctr b scalar/g' $(CURVE448_ODIR)/Curve_Ladder.ml
	$(OCAMLOPT) -I $(LIB_DIR_HST)/ml -I $(CURVE448_ODIR) $(addprefix $(LIB_DIR_HST)/ml/,$(REALIZED_ML_HST)) \
	  $(addprefix $(CURVE448_ODIR)/,$(CURVE448_EXTRACTED)) ml/test_curve448.ml -o test_curve448.exe
	./test_curve448.exe

# P256 HST extraction to OCaml
p256:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean all
	@mkdir -p $(P256_ODIR)
	@cp $(CODE_DIR_HST)/curve_specific/P256.Parameters.fst $(CODE_DIR_HST)/Curve.Parameters.fst
	@cp $(CODE_DIR_HST)/curve_specific/P256.Modulo.fst $(CODE_DIR_HST)/Curve.Modulo.fst
	@cp $(CODE_DIR_HST)/curve_specific/P256.Crecip.fst $(CODE_DIR_HST)/Curve.Crecip.fst
	@cp $(CODE_DIR_HST)/curve_specific/Curve.AddAndDoubleW.fst $(CODE_DIR_HST)/Curve.AddAndDouble.fst
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML_HST) $(LIB_FILES_HST) $(P256_FSTAR) --odir $(P256_ODIR)
	@rm $(addprefix $(CODE_DIR_HST)/Curve., Parameters.fst Modulo.fst Crecip.fst AddAndDouble.fst)
	@sed -i 's/(Obj.magic ((fun pp ppq p pq q n ctr b scalar/(((fun pp ppq p pq q n ctr b scalar/g' $(P256_ODIR)/Curve_Ladder.ml
	$(OCAMLOPT) -I $(LIB_DIR_HST)/ml -I $(P256_ODIR) $(addprefix $(LIB_DIR_HST)/ml/,$(REALIZED_ML_HST)) \
	  $(addprefix $(P256_ODIR)/,$(P256_EXTRACTED)) ml/test_p256.ml -o test_p256.exe
	# ./test_p256.exe

# Cleaning
clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	$(MAKE) -C $(LIB_DIR) clean
	$(MAKE) -C $(LIB_DIR_HST) clean
	@rm -f $(addprefix ml/, *.cmx *.o *.cmi *~) *~ *.exe
	@rm -rf $(CURVE25519_ODIR) $(CURVE448_ODIR) $(P256_ODIR)
