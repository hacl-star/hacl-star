# FStar variables
FSTAR_HOME?=../../../FStar
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_DEFAULT_ARGS) # from the included Makefile

HACL_DIR_HST=../../crypto_hst/utils
HACL_FILES_HST= $(addprefix $(HACL_DIR_HST)/, Hacl.Operations.fst Hacl.Conversions.fst)

LIB_DIR_HST=../../lib/hst
LIB_FILES_HST=$(addprefix $(LIB_DIR_HST)/, Math.Axioms.fst Math.Lib.fst Math.Lemmas.fst Hacl.UInt8.fst Hacl.UInt32.fst Hacl.UInt64.fst Hacl.UInt128.fst Hacl.SBuffer.fst Hacl.Cast.fst) $(HACL_FILES_HST)

OPTIONS_OCAML=--lax --codegen OCaml --no_location_info


# OCaml variables
OCAMLOPT := $(OCAMLOPT) -I $(ULIB_ML)/native_int -w -20-26

REALIZED_MLI_HST=Hacl_UInt8 Hacl_UInt32 Hacl_UInt64 Hacl_UInt128
REALIZED_HST=FStar_HyperStack FStar_HST Hacl_Cast Hacl_SBuffer Hacl_Utils
REALIZED_MODULE_HST=$(subst _,., $(REALIZED_HST))
REALIZED_ML_HST=$(addsuffix .mli,$(REALIZED_MLI_HST)) $(addsuffix .ml,$(REALIZED_MLI_HST) $(REALIZED_HST))
NO_CODEGEN_HST=$(addprefix --no_extract , $(REALIZED_MODULE_HST))


# Dependencies
SHA256_FSTAR_HST=../../crypto_hst/sha/Hash.Sha256.fst
SHA256_EXTRACTED_HST=Hacl_Operations.ml Hacl_Conversions.ml Hash_Sha256.ml

# Module
CODE_DIR_HST=../../crypto_hst/hmac
HMAC_SHA256_FSTAR_HST=$(addprefix $(CODE_DIR_HST)/, HMAC.B.fst)
HMAC_SHA256_EXTRACTED_HST=HMAC_B.ml

# Output
HMAC_SHA256_ODIR=hmac_sha256



.PHONY: hmac-sha256-ml hmac-sha256-compile

all: hmac-sha256-ml

hmac-sha256-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml
	mkdir -p $(HMAC_SHA256_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(LIB_FILES_HST) $(SHA256_FSTAR_HST) $(HMAC_SHA256_FSTAR_HST) --odir $(HMAC_SHA256_ODIR)
	$(OCAMLOPT) -I $(LIB_DIR_HST)/ml -I $(HMAC_SHA256_ODIR) $(addprefix $(LIB_DIR_HST)/ml/,$(REALIZED_ML_HST)) \
     $(addprefix $(HMAC_SHA256_ODIR)/,$(SHA256_EXTRACTED_HST)) \
	  $(addprefix $(HMAC_SHA256_ODIR)/,$(HMAC_SHA256_EXTRACTED_HST)) ml/test_hmac_sha256.ml -o test_hmac_sha256.exe
	./test_hmac_sha256.exe

hmac-sha256-pretty:
	cp hmac_sha256/HMAC_B.ml hmac_sha256/X.ml
	camlp4 pa_o.cmo pr_o.cmo hmac_sha256/X.ml > hmac_sha256/HMAC_B.ml

hmac-sha256-compile:
	$(OCAMLOPT) -I $(LIB_DIR_HST)/ml -I $(HMAC_SHA256_ODIR) $(addprefix $(LIB_DIR_HST)/ml/,$(REALIZED_ML_HST)) \
     $(addprefix $(HMAC_SHA256_ODIR)/,$(SHA256_EXTRACTED_HST)) \
	  $(addprefix $(HMAC_SHA256_ODIR)/,$(HMAC_SHA256_EXTRACTED_HST)) ml/test_hmac_sha256.ml -o test_hmac_sha256.exe
	./test_hmac_sha256.exe

# Cleaning
clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	$(MAKE) -C $(LIB_DIR_HST) clean
	@rm -f $(addprefix ml/, *.cmx *.o *.cmi *~) *~ *.exe
	@rm -rf $(HMAC_SHA256_ODIR)
