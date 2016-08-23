# FStar variables
FSTAR_HOME?=../../../FStar
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_DEFAULT_ARGS) # from the included Makefile

LIB_DIR=../../lib/st
LIB_FILES=$(addprefix $(LIB_DIR)/, axioms.fst intlib.fst IntLibLemmas.fst sint.fst sbuffer.fst SInt.UInt8.fst SInt.UInt32.fst SInt.UInt63.fst SInt.UInt64.fst SInt.Cast.fst SBytes.fst)

LIB_DIR_HST=../../lib/hst
LIB_FILES_HST=$(addprefix $(LIB_DIR_HST)/, Math.Axioms.fst Math.Lib.fst Math.Lemmas.fst Hacl.UInt8.fst Hacl.UInt32.fst Hacl.UInt64.fst Hacl.UInt128.fst Hacl.SBuffer.fst Hacl.Cast.fst)

CODE_DIR=../../crypto/symmetric
CODE_DIR_HST=../../crypto_hst/symmetric

KREMLIN_DIR=../../../fork/kremlin
KREMLIN=$(KREMLIN_DIR)/Kremlin.native
KREMLIN_LIB=$(KREMLIN_DIR)/kremlib
KREMLIN_ARGS=
KREMLIN_OBJS=kremlib.o testlib.o haclib.o
C_COMP=gcc -I$(LIB_DIR_HST)/c/

OPTIONS_OCAML=--lax --codegen OCaml --no_location_info --use_native_int
OPTIONS_OCAML_HST=--lax --codegen OCaml --no_location_info
OPTIONS_KREMLIN=--lax --codegen Kremlin

# OCaml variables
OCAMLOPT := $(OCAMLOPT) -w -20-26
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

# FStar ST files
CHACHA_FSTAR=$(addprefix $(CODE_DIR)/,chacha.fst)
POLY_FSTAR=$(addprefix $(CODE_DIR)/,parameters.fst bigint.fst bignum.fst poly.fst)
AES_FSTAR=$(addprefix $(CODE_DIR)/,Crypto.AES.fst)

# FStar HST files
CHACHA_FSTAR_HST=$(addprefix $(CODE_DIR_HST)/,Chacha20.fst)
POLY_FSTAR_HST=$(addprefix $(CODE_DIR_HST)/,Poly.Parameters.fst Poly.Bigint.fst Poly.Bignum.fst Poly.Poly1305.fst)
AES_FSTAR_HST=$(addprefix $(CODE_DIR_HST)/,Symmetric.AES.fst)
AESGCM_FSTAR_HST=$(addprefix $(CODE_DIR_HST)/,Symmetric.AES.fst GCM.fst AEAD.AES256_GCM.fst)

CHACHA_EXTRACTED=Chacha.ml
POLY_EXTRACTED=FStar_PredicateExtensionality.ml FStar_Seq.ml FStar_Ghost.ml Axioms.ml Parameters.ml Bigint.ml Bignum.ml Poly.ml
AES_EXTRACTED=Crypto_AES.ml

CHACHA_EXTRACTED_HST=Chacha20.ml
POLY_EXTRACTED_HST=FStar_FunctionalExtensionality.ml FStar_List_Tot.ml FStar_Seq.ml FStar_Ghost.ml Poly_Parameters.ml Poly_Bigint.ml Poly_Bignum.ml Poly_Poly1305.ml
AES_EXTRACTED_HST=Symmetric_AES.ml
AESGCM_EXTRACTED_HST=Symmetric_AES.ml GCM.ml AEAD_AES256_GCM.ml

CHACHA_EXTRACTED_C=Chacha20.c

CHACHA_ODIR=chacha20
POLY_ODIR=poly1305
AES_ODIR=aes
AESGCM_ODIR=aesgcm

.PHONY: chacha-ml poly-ml aes-ml chacha-hst-ml

all: chacha-hst-ml aes-hst-ml aes-gcm-hst-ml poly-hst-ml # chacha-ml poly-ml aes-ml 

# OCaml extracton of CHACHA20
chacha-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean all PRIMS_DIR=native_int
	mkdir -p $(CHACHA_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(LIB_FILES) $(CHACHA_FSTAR) --odir $(CHACHA_ODIR) 
	$(OCAMLOPT) -I $(ULIB_ML)/native_int -I $(LIB_DIR)/ml -I $(CHACHA_ODIR) $(addprefix $(LIB_DIR)/ml/,$(REALIZED_ML)) \
	  $(addprefix $(CHACHA_ODIR)/,$(CHACHA_EXTRACTED)) ml/test_chacha20.ml -o test_chacha20.exe 
	./test_chacha20.exe

# OCaml extracton of POLY1305
poly-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean all PRIMS_DIR=native_int
	mkdir -p $(POLY_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(LIB_FILES) $(POLY_FSTAR) --odir $(POLY_ODIR) #2> /dev/null
	$(OCAMLOPT) -I $(ULIB_ML)/native_int -I $(LIB_DIR)/ml -I $(POLY_ODIR) $(addprefix $(LIB_DIR)/ml/,$(REALIZED_ML)) \
	  $(addprefix $(POLY_ODIR)/,$(POLY_EXTRACTED)) ml/test_poly1305.ml -o test_poly1305.exe 
	./test_poly1305.exe

# OCaml extraction of AES
aes-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean all PRIMS_DIR=native_int
	mkdir -p $(AES_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(LIB_FILES) $(AES_FSTAR) --odir $(AES_ODIR) 
	$(OCAMLOPT) -I $(ULIB_ML)/native_int -I $(LIB_DIR)/ml -I $(AES_ODIR) $(addprefix $(LIB_DIR)/ml/,$(REALIZED_ML)) \
	  $(addprefix $(AES_ODIR)/,$(AES_EXTRACTED)) ml/test_aes.ml -o test_aes.exe
	./test_aes.exe

# OCaml extracton of CHACHA20
chacha-hst-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean all
	mkdir -p $(CHACHA_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML_HST) $(LIB_FILES_HST) $(CHACHA_FSTAR_HST) --odir $(CHACHA_ODIR) 
	$(OCAMLOPT) -I $(LIB_DIR_HST)/ml -I $(CHACHA_ODIR) $(addprefix $(LIB_DIR_HST)/ml/,$(REALIZED_ML_HST)) \
	  $(addprefix $(CHACHA_ODIR)/,$(CHACHA_EXTRACTED_HST)) ml/test_chacha_hst.ml -o test_chacha20.exe 
	./test_chacha20.exe

# C extraction of CHACHA20
chacha-c:
	$(C_COMP) -c $(KREMLIN_LIB)/kremlib.c
	$(C_COMP) -c $(KREMLIN_DIR)/test/testlib.c
	$(C_COMP) -c $(LIB_DIR_HST)/c/haclib.c
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean all
	mkdir -p $(CHACHA_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_KREMLIN) $(LIB_FILES_HST) $(CHACHA_FSTAR_HST) --odir $(CHACHA_ODIR)
	$(KREMLIN) -write out.krml $(KREMLIN_ARGS) -add-include \"haclib.h\"
	$(C_COMP) $(KREMLIN_OBJS) $(LIB_DIR_HST)/c/haclib.h ./c/test_chacha.c -o test_chacha.out
	./test_chacha.out

chacha-exe:
	$(KREMLIN) -write out.krml $(KREMLIN_ARGS) -add-include \"haclib.h\"
	$(C_COMP) $(KREMLIN_OBJS) $(LIB_DIR_HST)/c/haclib.h ./c/test_chacha.c -o test_chacha.out
	./test_chacha.out

poly-hst-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean all
	mkdir -p $(POLY_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML_HST) $(LIB_FILES_HST) $(POLY_FSTAR_HST) --odir $(POLY_ODIR) 
	$(OCAMLOPT) -I $(LIB_DIR_HST)/ml -I $(POLY_ODIR) $(addprefix $(LIB_DIR_HST)/ml/,$(REALIZED_ML_HST)) \
	  $(addprefix $(POLY_ODIR)/,$(POLY_EXTRACTED_HST)) ml/test_poly1305_hst.ml -o test_poly.exe 
	./test_poly.exe

# OCaml extracton of AES
aes-hst-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean all
	mkdir -p $(AES_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML_HST) $(LIB_FILES_HST) $(AES_FSTAR_HST) --odir $(AES_ODIR) 
	$(OCAMLOPT) -I $(LIB_DIR_HST)/ml -I $(AES_ODIR) $(addprefix $(LIB_DIR_HST)/ml/,$(REALIZED_ML_HST)) \
	  $(addprefix $(AES_ODIR)/,$(AES_EXTRACTED_HST)) ml/test_aes_hst.ml -o test_aes.exe 
	./test_aes.exe

# OCaml extracton of AES256GCM
aes-gcm-hst-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean all
	mkdir -p $(AESGCM_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML_HST) $(LIB_FILES_HST) $(AESGCM_FSTAR_HST) --odir $(AESGCM_ODIR) 
	$(OCAMLOPT) -I $(LIB_DIR_HST)/ml -I $(AESGCM_ODIR) $(addprefix $(LIB_DIR_HST)/ml/,$(REALIZED_ML_HST)) \
	  $(addprefix $(AESGCM_ODIR)/,$(AESGCM_EXTRACTED_HST)) ml/test_aes_gcm_hst.ml -o test_aes_gcm.exe 
	./test_aes_gcm.exe

compile:
	$(OCAMLOPT) -I $(LIB_DIR_HST)/ml -I $(CHACHA_ODIR) $(addprefix $(LIB_DIR_HST)/ml/,$(REALIZED_ML_HST)) \
	  $(addprefix $(CHACHA_ODIR)/,$(CHACHA_EXTRACTED_HST)) ml/test_chacha_hst.ml -o test_chacha20.exe 
	./test_chacha20.exe

# Cleaning
clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	rm -rf *.c *.out *.cmx *.o *.cmi *~ *.cmo *.exe *.krml $(CHACHA_ODIR) $(POLY_ODIR) $(AES_ODIR) $(AESGCM_ODIR) \
		$(addprefix $(LIB_DIR)/ml/,*.cmx *.o *.cmi *~ *.cmo) \
		$(addprefix $(LIB_DIR_HST)/ml/,*.cmx *.o *.cmi *~ *.cmo) \
		$(addprefix ml/,*.cmx *.o *.cmi *~ *.cmo) $(CODE_DIR)/*~
