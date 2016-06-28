# FStar variables
FSTAR_HOME?=../../../FStar
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_DEFAULT_ARGS) # from the included Makefile

LIB_DIR=../../lib/st
LIB_FILES=$(addprefix $(LIB_DIR)/, axioms.fst intlib.fst IntLibLemmas.fst sint.fst sbuffer.fst SInt.UInt8.fst SInt.UInt32.fst SInt.UInt63.fst SInt.UInt64.fst SInt.Cast.fst SBytes.fst)

CODE_DIR=../../crypto/hash

OPTIONS_OCAML=--lax --codegen OCaml --universes --no_location_info --use_native_int

# OCaml variables
OCAMLOPT := $(OCAMLOPT) -I $(ULIB_ML)/native_int -w -20-26
REALIZED_MLI=SInt_UInt8 SInt_UInt32 SInt_UInt63 SInt_UInt64
REALIZED=SInt_Cast SBuffer SBytes
REALIZED_MODULE=$(subst _,., $(REALIZED))
REALIZED_ML=$(addsuffix .mli,$(REALIZED_MLI)) $(addsuffix .ml,$(REALIZED_MLI) $(REALIZED))
NO_CODEGEN=$(addprefix --no_extract , SInt $(REALIZED_MODULE))

SHA1_FSTAR=$(addprefix $(CODE_DIR)/, \ # TODO: add F* code module for HASH functions. e.g.: hash.fst
	)
SHA1_EXTRACTED= # TODO: add extracted module names to compile

# TODO: add same variables for other SHA, HMAC etc.

SHA1_ODIR=sha1

.PHONY: sha1-ml # TOOD: add other relevant targets

all: sha1-ml

# SHA1 extraction to OCaml
sha1-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml PRIMS_DIR=native_int
	mkdir -p $(_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(LIB_FILES) $(SHA1_FSTAR) --odir $(SHA1_ODIR)
	$(OCAMLOPT) -I $(LIB_DIR)/ml -I $(SHA1_ODIR) $(addprefix $(LIB_DIR)/ml/,$(REALIZED_ML)) \
	  $(addprefix $(SHA1_ODIR)/,$(SHA1_EXTRACTED)) ml/test_sha1.ml -o test_sha1.exe
	./test_sha1.exe

# Cleaning
clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	$(MAKE) -C $(LIB_DIR) clean
	@rm -f $(addprefix ml/, *.cmx *.o *.cmi *~) *~ *.exe
	@rm -rf $(SHA1_ODIR)
