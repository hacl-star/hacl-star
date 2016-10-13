# FStar variables
FSTAR_HOME?=../../../FStar
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_DEFAULT_ARGS) # from the included Makefile

LIB_DIR_HST=../../lib/hst
LIB_FILES_HST=$(addprefix $(LIB_DIR_HST)/, Hacl.UInt8.fst Hacl.UInt32.fst Hacl.UInt64.fst Hacl.UInt128.fst Hacl.SBuffer.fst Hacl.Cast.fst)

CODE_DIR_HST=../../crypto_hst/symmetric

KREMLIN_DIR?=../../../kremlin
KREMLIN=$(KREMLIN_DIR)/Kremlin.native
KREMLIN_LIB=$(KREMLIN_DIR)/kremlib
KREMLIN_ARGS=-verbose

OPTIONS_OCAML=--lax --codegen OCaml --no_location_info --use_native_int
OPTIONS_OCAML_HST=--lax --codegen OCaml --no_location_info
OPTIONS_KREMLIN=--lax --codegen Kremlin
HACL_KREMLIN_LIB=$(addprefix $(LIB_DIR_HST)/kremlin/, Hacl.UInt8.fst Hacl.UInt32.fst Hacl.UInt64.fst Hacl.UInt128.fst Hacl.SBuffer.fst Hacl.Cast.fst)

# OCaml variables
OCAMLOPT := $(OCAMLOPT) -w -20-26

# OCaml HST variables
REALIZED_MLI_HST=Hacl_UInt8 Hacl_UInt32 Hacl_UInt64 Hacl_UInt128
REALIZED_HST=Hacl_Cast Hacl_SBuffer
REALIZED_MODULE_HST=$(subst _,., $(REALIZED_HST))
REALIZED_ML_HST=$(addsuffix .mli,$(REALIZED_MLI_HST)) $(addsuffix .ml,$(REALIZED_MLI_HST) $(REALIZED_HST))
NO_CODEGEN_HST=$(addprefix --no_extract , $(REALIZED_MODULE_HST))

# FStar HST files
CHACHA_FSTAR_HST=$(addprefix $(CODE_DIR_HST)/,Hacl.Symmetric.Chacha20.fst)
SALSA_FSTAR_HST=$(addprefix $(CODE_DIR_HST)/,Hacl.Symmetric.Salsa20.fst)
AES_FSTAR_HST=$(addprefix $(CODE_DIR_HST)/,Hacl.Symmetric.AES.fst)
AESGCM_FSTAR_HST=$(addprefix $(CODE_DIR_HST)/,Hacl.Symmetric.AES.fst Hacl.Symmetric.GCM.fst Hacl.AEAD.AES256GCM.fst)
POLY1305_FSTAR=$(addprefix $(CODE_DIR_HST)/,Hacl.Symmetric.Poly1305.fst)

CHACHA_EXTRACTED=Chacha.ml
POLY_EXTRACTED=FStar_PredicateExtensionality.ml FStar_Seq.ml FStar_Ghost.ml Axioms.ml Parameters.ml Bigint.ml Bignum.ml Poly.ml
AES_EXTRACTED=Crypto_AES.ml

CHACHA_EXTRACTED_HST=Hacl_Symmetric_Chacha20.ml
SALSA_EXTRACTED_HST=Hacl_Symmetric_Salsa20.ml
AES_EXTRACTED_HST=Hacl_Symmetric_AES.ml
AESGCM_EXTRACTED_HST=Hacl_Symmetric_AES.ml Hacl_Symmetric_GCM.ml Hacl_AEAD_AES256GCM.ml
POLY1305_EXTRACTED=FStar_FunctionalExtensionality.ml FStar_List_Tot.ml FStar_Seq.ml FStar_Ghost.ml Utils.ml Hacl_Symmetric_Poly1305_Parameters.ml Hacl_Symmetric_Poly1305_Bigint.ml Hacl_Symmetric_Poly1305_Bignum.ml Hacl_Symmetric_Poly1305.ml

CHACHA_ODIR=chacha20
SALSA_ODIR=salsa20
XSALSA_ODIR=xsalsa20
POLY_ODIR=poly1305
AES_ODIR=aes
CHACHAPOLY_ODIR=chachapoly
AESGCM_ODIR=aesgcm

.PHONY:

all:
	$(MAKE) ml-lib
	$(MAKE) ml
	$(MAKE) kremlin

ml: 		chacha-test aes-test aes-gcm-test
kremlin: 	kremlin_chacha20.exe kremlin_salsa20.exe kremlin_xsalsa20.exe \
		kremlin_poly1305.exe kremlin_chachapoly.exe

clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	rm -rf *.c *.h *.out *.cmx *.o *.cmi *~ *.cmo *.exe *.krml \
		$(CHACHA_ODIR) $(POLY_ODIR) $(AES_ODIR) $(AESGCM_ODIR) $(SALSA_ODIR) $(XSALSA_ODIR) \
		$(CHACHAPOLY_ODIR) \
		$(addprefix $(LIB_DIR)/ml/,*.cmx *.o *.cmi *~ *.cmo) \
		$(addprefix $(LIB_DIR_HST)/ml/,*.cmx *.o *.cmi *~ *.cmo) \
		$(addprefix ml/,*.cmx *.o *.cmi *~ *.cmo) $(CODE_DIR)/*~

#################
# OCAML TARGETS #
#################

ml-lib:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml all

# OCaml extracton of CHACHA20
chacha-extract: ml-lib
	mkdir -p $(CHACHA_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML_HST) $(LIB_FILES_HST) $(CHACHA_FSTAR_HST) --odir $(CHACHA_ODIR)

chacha-compile: chacha-extract
	$(OCAMLOPT) -I $(LIB_DIR_HST)/ml -I $(CHACHA_ODIR) \
	  $(addprefix $(LIB_DIR_HST)/ml/,$(REALIZED_ML_HST)) \
	  $(addprefix $(CHACHA_ODIR)/,$(CHACHA_EXTRACTED_HST)) ml/test_chacha_hst.ml -o test_chacha20.exe

chacha-test: chacha-compile
	./test_chacha20.exe

salsa-extract: ml-lib
	mkdir -p $(SALSA_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML_HST) $(LIB_FILES_HST) $(SALSA_FSTAR_HST) --odir $(SALSA_ODIR)

salsa-compile: salsa-extract
	$(OCAMLOPT) -I $(LIB_DIR_HST)/ml -I $(SALSA_ODIR) \
	  $(addprefix $(LIB_DIR_HST)/ml/,$(REALIZED_ML_HST)) \
	  $(addprefix $(SALSA_ODIR)/,$(SALSA_EXTRACTED_HST)) ml/test_salsa_hst.ml -o test_salsa20.exe

salsa-test: salsa-compile
	./test_salsa20.exe

# OCaml extracton of POLY1305
poly-extract: ml-lib
	mkdir -p $(POLY_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML_HST) $(LIB_FILES_HST) $(POLY1305_FSTAR) --odir $(POLY_ODIR) --include $(CODE_DIR_HST)

poly-compile: poly-extract
	$(OCAMLOPT) -I $(LIB_DIR_HST)/ml -I $(POLY_ODIR) \
		$(addprefix $(LIB_DIR_HST)/ml/,$(REALIZED_ML_HST)) \
	  	$(addprefix $(POLY_ODIR)/,$(POLY1305_EXTRACTED)) ml/test_poly1305_hst.ml -o test_poly.exe

poly-test: poly-compile
	./test_poly.exe

# OCaml extracton of AES
aes-extract: ml-lib
	mkdir -p $(AES_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML_HST) $(LIB_FILES_HST) $(AES_FSTAR_HST) --odir $(AES_ODIR)

aes-compile: aes-extract
	$(OCAMLOPT) -I $(LIB_DIR_HST)/ml -I $(AES_ODIR) \
	  $(addprefix $(LIB_DIR_HST)/ml/,$(REALIZED_ML_HST)) \
	  $(addprefix $(AES_ODIR)/,$(AES_EXTRACTED_HST)) ml/test_aes_hst.ml -o test_aes.exe 

aes-test: aes-compile
	./test_aes.exe

# OCaml extracton of AES256GCM
aes-gcm-extract: ml-lib
	mkdir -p $(AESGCM_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML_HST) $(LIB_FILES_HST) $(AESGCM_FSTAR_HST) --odir $(AESGCM_ODIR) 

aes-gcm-compile: aes-gcm-extract
	$(OCAMLOPT) -I $(LIB_DIR_HST)/ml -I $(AESGCM_ODIR) \
	  $(addprefix $(LIB_DIR_HST)/ml/,$(REALIZED_ML_HST)) \
	  $(addprefix $(AESGCM_ODIR)/,$(AESGCM_EXTRACTED_HST)) ml/test_aes_gcm_hst.ml -o test_aes_gcm.exe

aes-gcm-test: aes-gcm-compile
	./test_aes_gcm.exe


#######################
# KREMLIN (C) TARGETS #
#######################

kremlin_chacha20.exe: $(CODE_DIR_HST)/Hacl.Symmetric.Chacha20.fst
	mkdir -p $(CHACHA_ODIR)
	$(KREMLIN) $(KREMLIN_ARGS) $(HACL_KREMLIN_LIB) \
		-I $(CODE_DIR_HST) -I $(KREMLIN_DIR)/test \
		$(KREMLIN_DIR)/test/testlib.c c/test_chacha.c $^ \
		-tmpdir $(CHACHA_ODIR) -o $@
	./$@

kremlin_salsa20.exe: $(CODE_DIR_HST)/Hacl.Symmetric.Salsa20.fst
	mkdir -p $(SALSA_ODIR)
	$(KREMLIN) $(KREMLIN_ARGS) $(HACL_KREMLIN_LIB) \
		-I $(CODE_DIR_HST) -I $(KREMLIN_DIR)/test/ \
		$(KREMLIN_DIR)/test/testlib.c c/test_salsa20.c $^ \
		-tmpdir $(SALSA_ODIR) -o $@
	./$@

kremlin_xsalsa20.exe: $(CODE_DIR_HST)/Hacl.Symmetric.XSalsa20.fst
	mkdir -p $(XSALSA_ODIR)
	$(KREMLIN) $(KREMLIN_ARGS) $(HACL_KREMLIN_LIB) \
		-I $(CODE_DIR_HST) -I $(KREMLIN_DIR)/test/ \
		$(KREMLIN_DIR)/test/testlib.c c/test_xsalsa20.c $^ \
		-tmpdir $(XSALSA_ODIR) -o $@
	./$@

kremlin_poly1305.exe: $(CODE_DIR_HST)/Hacl.Symmetric.Poly1305.fst
	mkdir -p $(POLY_ODIR)
	$(KREMLIN) $(KREMLIN_ARGS) $(HACL_KREMLIN_LIB) \
		-I $(CODE_DIR_HST) -I $(KREMLIN_DIR)/test/ \
		$(KREMLIN_DIR)/test/testlib.c c/test_poly.c $^ \
		-tmpdir $(POLY_ODIR) -o $@
	./$@

kremlin_chachapoly.exe: $(CODE_DIR_HST)/Hacl.AEAD.Chacha20Poly1305.fst
	mkdir -p $(CHACHAPOLY_ODIR)
	$(KREMLIN) $(KREMLIN_ARGS) $(HACL_KREMLIN_LIB) \
		-I $(CODE_DIR_HST) -I $(KREMLIN_DIR)/test/ \
		$(KREMLIN_DIR)/test/testlib.c c/test_aead_chacha_poly.c $^ \
		-tmpdir $(CHACHAPOLY_ODIR) -o $@
	./$@

kremlin: 	kremlin_chacha20.exe \
		kremlin_salsa20.exe \
		kremlin_xsalsa20.exe \
		kremlin_poly1305.exe \
		kremlin_chachapoly.exe
