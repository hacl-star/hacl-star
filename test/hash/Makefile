# FStar variables
FSTAR_HOME?=../../../FStar
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_DEFAULT_ARGS) # from the included Makefile

HACL_DIR_HST=../../crypto_hst/utils
HACL_FILES_HST= $(addprefix $(HACL_DIR_HST)/, Hacl.Operations.fst Hacl.Conversions.fst)

LIB_DIR_HST=../../lib/hst
LIB_FILES_HST=$(addprefix $(LIB_DIR_HST)/, Math.Axioms.fst Math.Lib.fst Math.Lemmas.fst Math.Logic.Axioms.fst Hacl.UInt8.fst Hacl.UInt16.fst Hacl.UInt32.fst Hacl.UInt64.fst Hacl.UInt128.fst Hacl.SBuffer.fst Hacl.Cast.fst) $(HACL_FILES_HST)

OPTIONS_OCAML=--lax --codegen OCaml --no_location_info


# OCaml variables
OCAMLOPT := $(OCAMLOPT) -I $(ULIB_ML)/native_int -w -20-26

REALIZED_MLI_HST=Hacl_UInt8 Hacl_UInt16 Hacl_UInt32 Hacl_UInt64 Hacl_UInt128
REALIZED_HST= Hacl_Cast Hacl_SBuffer Hacl_Utils
REALIZED_MODULE_HST=$(subst _,., $(REALIZED_HST))
REALIZED_ML_HST=$(addsuffix .mli,$(REALIZED_MLI_HST)) $(addsuffix .ml,$(REALIZED_MLI_HST) $(REALIZED_HST))
NO_CODEGEN_HST=$(addprefix --no_extract , $(REALIZED_MODULE_HST))


# Module
CODE_DIR_HST=../../crypto_hst/hash

# Base files
SHA2_EXTRACTED_HST_BASE=Hacl_Operations.ml Hacl_Conversions.ml

# Output
SHA2_ODIR=sha2

# SHA2-256
SHA2_256_FSTAR_HST= Hash.SHA2.L256.fst
SHA2_256_EXTRACTED_HST= Hash_SHA2_L256.ml
SHA2_256_FSTAR_HST_R=$(addprefix $(CODE_DIR_HST)/, $(SHA2_256_FSTAR_HST))
SHA2_256_ML=$(SHA2_EXTRACTED_HST_BASE) $(SHA2_256_EXTRACTED_HST)
SHA2_256_ODIR=$(SHA2_ODIR)-256
SHA2_256_TEST=test-$(SHA2_ODIR)-256


# Targets
.PHONY: sha2-256-ml sha2-256-pretty sha2-256-compile

all: sha2-256-ml sha2-256-compile

sha2-256-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml
	mkdir -p $(SHA2_256_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(LIB_FILES_HST) $(HACL_FILES_HST) $(SHA2_256_FSTAR_HST_R) --odir $(SHA2_256_ODIR)

sha2-256-pretty:
	cp $(SHA2_256_ODIR)/$(SHA2_256_EXTRACTED_HST) $(SHA2_256_ODIR)/X.ml
	camlp4 pa_o.cmo pr_o.cmo  $(SHA2_256_ODIR)/X.ml > $(SHA2_256_ODIR)/$(SHA2_256_EXTRACTED_HST)

sha2-256-compile:
	$(OCAMLOPT) -I $(LIB_DIR_HST)/ml -I $(SHA2_256_ODIR) $(addprefix $(LIB_DIR_HST)/ml/,$(REALIZED_ML_HST)) \
	  $(addprefix $(SHA2_256_ODIR)/,$(SHA2_256_ML)) ml/$(SHA2_256_TEST).ml -o $(SHA2_256_TEST).exe
	./$(SHA2_256_TEST).exe

# Cleaning
clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	$(MAKE) -C $(LIB_DIR_HST) clean
	@rm -f $(addprefix ml/, *.cmx *.o *.cmi *~) *~ *.exe
	@rm -rf $(SHA2_ODIR) $(SHA2_256_ODIR)
