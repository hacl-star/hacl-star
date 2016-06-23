# FStar variables
FSTAR_HOME?=../../../FStar
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_DEFAULT_ARGS) # from the included Makefile

LIB_DIR=../../lib/st
LIB_FILES=$(addprefix $(LIB_DIR)/, axioms.fst intlib.fst IntLibLemmas.fst sint.fst sbuffer.fst SInt.UInt8.fst SInt.UInt32.fst SInt.UInt63.fst SInt.UInt64.fst SInt.Cast.fst SBytes.fst)

CODE_DIR=../../crypto/symetric

OPTIONS_OCAML=--lax --codegen OCaml --universes --no_location_info --use_native_int

# OCaml variables
OCAMLOPT := $(OCAMLOPT) -I $(ULIB_ML)/native_int -w -20-26
REALIZED_MLI=SInt_UInt8 SInt_UInt32 SInt_UInt63 SInt_UInt64
REALIZED=SInt_Cast SBuffer SBytes
REALIZED_MODULE=$(subst _,., $(REALIZED))
REALIZED_ML=$(addsuffix .mli,$(REALIZED_MLI)) $(addsuffix .ml,$(REALIZED_MLI) $(REALIZED))
NO_CODEGEN=$(addprefix --no_extract , SInt $(REALIZED_MODULE))

CHACHA_FSTAR=$(addprefix $(CODE_DIR)/,chacha.fst)
POLY_FSTAR=$(addprefix $(CODE_DIR)/,parameters.fst bigint.fst bignum.fst poly.fst)
AES_FSTAR=$(addprefix $(CODE_DIR)/,Crypto.AES.fst)

CHACHA_EXTRACTED=Chacha.ml
POLY_EXTRACTED=FStar_FunctionalExtensionality.ml FStar_Seq.ml FStar_Ghost.ml Axioms.ml Parameters.ml Bigint.ml Bignum.ml Poly.ml
AES_EXTRACTED=Crypto_AES.ml

CHACHA_ODIR=chacha20
POLY_ODIR=poly1305
AES_ODIR=aes

.PHONY: chacha-ml poly-ml aes-ml

all: chacha-ml poly-ml aes-ml

# OCaml extracton of CHACHA20
chacha-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml PRIMS_DIR=native_int
	mkdir -p $(CHACHA_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(LIB_FILES) $(CHACHA_FSTAR) --odir $(CHACHA_ODIR) 
	$(OCAMLOPT) -I $(LIB_DIR)/ml -I $(CHACHA_ODIR) $(addprefix $(LIB_DIR)/ml/,$(REALIZED_ML)) \
	  $(addprefix $(CHACHA_ODIR)/,$(CHACHA_EXTRACTED)) ml/test_chacha20.ml -o test_chacha20.exe 
	./test_chacha20.exe

# OCaml extracton of POLY1305
poly-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml PRIMS_DIR=native_int
	mkdir -p $(POLY_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(LIB_FILES) $(POLY_FSTAR) --odir $(POLY_ODIR) #2> /dev/null
	$(OCAMLOPT) -I $(LIB_DIR)/ml -I $(POLY_ODIR) $(addprefix $(LIB_DIR)/ml/,$(REALIZED_ML)) \
	  $(addprefix $(POLY_ODIR)/,$(POLY_EXTRACTED)) ml/test_poly1305.ml -o test_poly1305.exe 
	./test_poly1305.exe

# OCaml extraction of AES
aes-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml PRIMS_DIR=native_int
	mkdir -p $(AES_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(LIB_FILES) $(AES_FSTAR) --odir $(AES_ODIR) 
	$(OCAMLOPT) -I $(LIB_DIR)/ml -I $(AES_ODIR) $(addprefix $(LIB_DIR)/ml/,$(REALIZED_ML)) \
	  $(addprefix $(AES_ODIR)/,$(AES_EXTRACTED)) ml/test_aes.ml -o test_aes.exe
	./test_aes.exe

# Cleaning
clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	rm -rf $ *.cmx *.o *.cmi *~ *.cmo *.exe $(CHACHA_ODIR) $(POLY_ODIR) $(AES_ODIR) \
		$(addprefix $(LIB_DIR)/ml/,*.cmx *.o *.cmi *~ *.cmo) ml/*~ $(CODE_DIR)/*~
