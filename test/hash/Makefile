# FStar variables
FSTAR_HOME?=../../../FStar
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_DEFAULT_ARGS) # from the included Makefile

LIB_DIR=../../lib/st
LIB_FILES=$(addprefix $(LIB_DIR)/, axioms.fst intlib.fst IntLibLemmas.fst sint.fst sbuffer.fst SInt.UInt8.fst SInt.UInt32.fst SInt.UInt63.fst SInt.UInt64.fst SInt.Cast.fst SBytes.fst)
LIB_DIR_HST=../../lib/hst
LIB_FILES_HST=$(addprefix $(LIB_DIR_HST)/, Math.Axioms.fst Math.Lib.fst Math.Lemmas.fst Hacl.UInt8.fst Hacl.UInt32.fst Hacl.UInt64.fst Hacl.SBuffer.fst Hacl.Cast.fst)

OPTIONS_OCAML=--lax --codegen OCaml --no_location_info


# OCaml variables
OCAMLOPT := $(OCAMLOPT) -I $(ULIB_ML)/native_int -w -20-26
REALIZED_MLI=SInt_UInt8 SInt_UInt32 SInt_UInt63 SInt_UInt64
REALIZED=SInt_Cast SBuffer SBytes
REALIZED_MODULE=$(subst _,., $(REALIZED))
REALIZED_ML=$(addsuffix .mli,$(REALIZED_MLI)) $(addsuffix .ml,$(REALIZED_MLI) $(REALIZED))
NO_CODEGEN=$(addprefix --no_extract , SInt $(REALIZED_MODULE))

REALIZED_MLI_HST=Hacl_UInt8 Hacl_UInt32 Hacl_UInt64
REALIZED_HST=FStar_HyperStack FStar_HST Hacl_Cast Hacl_SBuffer
REALIZED_MODULE_HST=$(subst _,., $(REALIZED_HST))
REALIZED_ML_HST=$(addsuffix .mli,$(REALIZED_MLI_HST)) $(addsuffix .ml,$(REALIZED_MLI_HST) $(REALIZED_HST))
NO_CODEGEN_HST=$(addprefix --no_extract , $(REALIZED_MODULE_HST))


# Module
CODE_DIR=../../crypto/sha
CODE_DIR_HST=../../crypto_hst/sha

SHA2_FSTAR_HST=$(addprefix $(CODE_DIR_HST)/, Hash.Sha256.fst)
SHA2_EXTRACTED_HST=Hash_Sha256.ml


# Output
SHA2_ODIR=sha256


.PHONY: sha256-ml sha256-compile

all: sha256-ml

sha256-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml
	mkdir -p $(SHA2_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(LIB_FILES_HST) $(SHA2_FSTAR_HST) --odir $(SHA2_ODIR)
	$(OCAMLOPT) -I $(LIB_DIR_HST)/ml -I $(SHA2_ODIR) $(addprefix $(LIB_DIR_HST)/ml/,$(REALIZED_ML_HST)) \
	  $(addprefix $(SHA2_ODIR)/,$(SHA2_EXTRACTED_HST)) ml/test_sha256.ml -o test_sha256.exe
	./test_sha256.exe

sha256-compile:
	$(OCAMLOPT) -I $(LIB_DIR_HST)/ml -I $(SHA2_ODIR) $(addprefix $(LIB_DIR_HST)/ml/,$(REALIZED_ML_HST)) \
	  $(addprefix $(SHA2_ODIR)/,$(SHA2_EXTRACTED_HST)) ml/test_sha256.ml -o test_sha256.exe
	./test_sha256.exe

# Cleaning
clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	$(MAKE) -C $(LIB_DIR) clean
	$(MAKE) -C $(LIB_DIR_HST) clean
	@rm -f $(addprefix ml/, *.cmx *.o *.cmi *~) *~ *.exe
	@rm -rf $(SHA2_ODIR)
