all: test-kremlin test-ocaml

FSTAR_HOME?=../../../FStar
KREMLIN_HOME?=../../../kremlin
HACL_HOME?=../..
include $(HACL_HOME)/lib/hyperstack/Makefile.include
KREMLIN_INCLUDES=$(addprefix -I , $(HACL_KREMLIN) $(HACL_SYMMETRIC) . $(KREMTEST)) \
	$(KREMTEST)/testlib.c -add-include \"testlib.h\"
OCAML_INCLUDES=$(addprefix --include , $(HACL_KREMLIN) $(HACL_SYMMETRIC) $(OCAML_LIB))

TEST_CHACHA20=Hacl.Test.Chacha20
#TEST_SALSA20=Hacl.Test.Salsa20
#TEST_XSALSA20=Hacl.Test.XSalsa20
TEST_POLY1305=Hacl.Test.Poly1305
TESTS=$(TEST_CHACHA20) $(TEST_SALSA20) $(TEST_XSALSA20) $(TEST_POLY1305) Hacl.Test2.Salsa20

.PHONY:test-kremlin

###################
# KREMLIN TARGETS #
###################

test-kremlin: $(addsuffix -krml, $(TESTS))
test-ocaml: #chacha-test salsa-test poly-test aes-test

%-krml: %.fst
	mkdir -p $(subst .,_,$(basename $^))
	$(KREMLIN) $(KREMLIN_ARGS) $(KREMLIN_INCLUDES) -no-prefix $(basename $^) $^ \
		 -warn-error -1-2-3-4-5-6 \
		-tmpdir $(subst .,_,$(basename $^)) -o $(subst .,_,$(basename $^)).exe
	./$(subst .,_,$(basename $^)).exe

clean:
	make -C $(HACL_LIB) clean
	rm -rf *.c *.h *.out *.cmx *.o *.cmi *~ *.cmo *.exe *.krml \
		$(subst .,_,$(TESTS)) $(CHACHA_ODIR) $(POLY_ODIR) $(AES_ODIR) \
		$(AESGCM_ODIR) $(SALSA_ODIR) $(XSALSA_ODIR) $(CHACHAPOLY_ODIR)
	rm -f $(addprefix ./ml/, *~ *.o *.cmx *.cmi *.cmo)

# OCaml variables
REALIZED_MLI_HST=Hacl_UInt8 Hacl_UInt32 Hacl_UInt64 Hacl_UInt128
REALIZED_HST=Hacl_Cast Hacl_SBuffer
REALIZED_MODULE_HST=$(subst _,., $(REALIZED_HST))
REALIZED_ML_HST=$(addsuffix .mli,$(REALIZED_MLI_HST)) $(addsuffix .ml,$(REALIZED_MLI_HST) $(REALIZED_HST))
NO_CODEGEN_HST=$(addprefix --no_extract , $(REALIZED_MODULE_HST))

# FStar files
CHACHA_FSTAR_HST=$(addprefix $(HACL_SYMMETRIC)/,Hacl.Symmetric.Chacha20.fst)
SALSA_FSTAR_HST=$(addprefix $(HACL_SYMMETRIC)/,Hacl.Symmetric.Salsa20.fst)
AES_FSTAR_HST=$(addprefix $(HACL_SYMMETRIC)/,Hacl.Symmetric.AES.fst)
AESGCM_FSTAR_HST=$(addprefix $(HACL_SYMMETRIC)/,Hacl.Symmetric.AES.fst Hacl.Symmetric.GCM.fst Hacl.AEAD.AES256GCM.fst)
POLY1305_FSTAR=$(addprefix $(HACL_SYMMETRIC)/,Hacl.Symmetric.Poly1305.fst)

CHACHA_EXTRACTED_HST=Utils.ml Hacl_Symmetric_Chacha20.ml
SALSA_EXTRACTED_HST=Utils.ml Hacl_Symmetric_Salsa20.ml
AES_EXTRACTED_HST=Hacl_Symmetric_AES.ml
AESGCM_EXTRACTED_HST=Hacl_Symmetric_AES.ml Hacl_Symmetric_GCM.ml Hacl_AEAD_AES256GCM.ml
POLY1305_EXTRACTED=FStar_FunctionalExtensionality.ml FStar_List_Tot.ml FStar_Seq.ml FStar_Ghost.ml Utils.ml Hacl_Symmetric_Poly1305_Parameters.ml Hacl_Symmetric_Poly1305_Bigint.ml Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part1.ml Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part2.ml Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part3.ml Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part4.ml Hacl_Symmetric_Poly1305_Bignum_Lemmas_Part5.ml Hacl_Symmetric_Poly1305_Bignum.ml Hacl_Symmetric_Poly1305_Spec.ml Hacl_Symmetric_Poly1305.ml

CHACHA_ODIR=chacha20
SALSA_ODIR=salsa20
XSALSA_ODIR=xsalsa20
POLY_ODIR=poly1305
AES_ODIR=aes
CHACHAPOLY_ODIR=chachapoly
AESGCM_ODIR=aesgcm

#################
# OCAML TARGETS #
#################

# OCaml extracton of CHACHA20
chacha-extract: ml-lib
	mkdir -p $(CHACHA_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OCAML_OPTIONS) $(OCAML_INCLUDES) $(CHACHA_FSTAR_HST) --odir $(CHACHA_ODIR)

chacha-compile: #chacha-extract
	$(OCAMLOPT) -I $(HACL_LIB)/ml -I $(CHACHA_ODIR) \
	  $(addprefix $(HACL_LIB)/ml/,$(REALIZED_ML_HST)) \
	  $(addprefix $(CHACHA_ODIR)/,$(CHACHA_EXTRACTED_HST)) ml/test_chacha_hst.ml -o test_chacha20.exe

chacha-test: chacha-compile
	./test_chacha20.exe

salsa-extract: ml-lib
	mkdir -p $(SALSA_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OCAML_OPTIONS) $(OCAML_INCLUDES) $(HACL_KREMLIN_LIB) $(SALSA_FSTAR_HST) --odir $(SALSA_ODIR) --include $(HACL_SYMMETRIC)

salsa-compile: salsa-extract
	$(OCAMLOPT) -I $(HACL_LIB)/ml -I $(SALSA_ODIR) \
	  $(addprefix $(HACL_LIB)/ml/,$(REALIZED_ML_HST)) \
	  $(addprefix $(SALSA_ODIR)/,$(SALSA_EXTRACTED_HST)) ml/test_salsa_hst.ml -o test_salsa20.exe

salsa-test: salsa-compile
	./test_salsa20.exe

# OCaml extracton of POLY1305
poly-extract: ml-lib
	mkdir -p $(POLY_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OCAML_OPTIONS) $(OCAML_INCLUDES) $(POLY1305_FSTAR) --odir $(POLY_ODIR) --include $(HACL_SYMMETRIC)

poly-compile: poly-extract
	$(OCAMLOPT) -I $(HACL_LIB)/ml -I $(POLY_ODIR) \
		$(addprefix $(HACL_LIB)/ml/,$(REALIZED_ML_HST)) \
	  	$(addprefix $(POLY_ODIR)/,$(POLY1305_EXTRACTED)) ml/test_poly1305_hst.ml -o test_poly.exe

poly-test: poly-compile
	./test_poly.exe

# OCaml extracton of AES
aes-extract: ml-lib
	mkdir -p $(AES_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OCAML_OPTIONS) $(OCAML_INCLUDES) $(AES_FSTAR_HST) --odir $(AES_ODIR)

aes-compile: aes-extract
	$(OCAMLOPT) -I $(HACL_LIB)/ml -I $(AES_ODIR) \
	  $(addprefix $(HACL_LIB)/ml/,$(REALIZED_ML_HST)) \
	  $(addprefix $(AES_ODIR)/,$(AES_EXTRACTED_HST)) ml/test_aes_hst.ml -o test_aes.exe 

aes-test: aes-compile
	./test_aes.exe

# OCaml extracton of AES256GCM
aes-gcm-extract: ml-lib
	mkdir -p $(AESGCM_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OCAML_OPTIONS) $(OCAML_INCLUDES) $(AESGCM_FSTAR_HST) --odir $(AESGCM_ODIR) 

aes-gcm-compile: aes-gcm-extract
	$(OCAMLOPT) -I $(HACL_LIB)/ml -I $(AESGCM_ODIR) \
	  $(addprefix $(HACL_LIB)/ml/,$(REALIZED_ML_HST)) \
	  $(addprefix $(AESGCM_ODIR)/,$(AESGCM_EXTRACTED_HST)) ml/test_aes_gcm_hst.ml -o test_aes_gcm.exe

aes-gcm-test: aes-gcm-compile
	./test_aes_gcm.exe

#OCaml extraction of the 64-bit version of Poly1305
poly64-extract: ml-lib
	mkdir -p $(POLY_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OCAML_OPTIONS) $(OCAML_INCLUDES) --odir $(POLY_ODIR) --include $(HACL_SYMMETRIC) Hacl.Test.Poly1305_64.fst --include $(KREMLIB) --include $(KREMTEST)
	echo "let _ = main()" >> $(POLY_ODIR)/Hacl_Test_Poly1305_64.ml

POLY1305_64_EXTRACTED=FStar_FunctionalExtensionality.ml FStar_List_Tot.ml FStar_Seq.ml FStar_Ghost.ml	Hacl_Symmetric_Poly1305_64_Parameters.ml Hacl_Symmetric_Poly1305_64_Bigint.ml Hacl_Symmetric_Poly1305_64.ml Hacl_Test_Poly1305_64.ml

poly64-compile: #poly64-extract
	$(OCAMLOPT) -I $(HACL_LIB)/ml -I $(POLY_ODIR) -I $(KREMTEST) -I $(KREMLIB) \
		$(addprefix $(HACL_LIB)/ml/,$(REALIZED_ML_HST)) \
		$(KREMTEST)/TestLib.ml $(KREMLIB)/C.ml \
	  	$(addprefix $(POLY_ODIR)/,$(POLY1305_64_EXTRACTED))  -o test_poly.exe

poly64-test: poly64-compile
	./test_poly.exe

chacha-sodium-extract: ml-lib
	mkdir -p chachasodium
	$(FSTAR) $(NO_CODEGEN) $(OCAML_OPTIONS) $(OCAML_INCLUDES) --odir chachasodium --include $(HACL_SYMMETRIC) Hacl.Test.Chacha20.Sodium.fst --include $(KREMLIB) --include $(KREMTEST)
	echo "let _ = main()" >> chachasodium/Hacl_Test_Chacha20_Sodium.ml

chacha-sodium-compile:
	$(OCAMLOPT) -I $(HACL_LIB)/ml -I chachasodium -I $(KREMTEST) -I $(KREMLIB) \
		$(addprefix $(HACL_LIB)/ml/,$(REALIZED_ML_HST)) \
		$(KREMTEST)/TestLib.ml $(KREMLIB)/C.ml \
	  	$(addprefix chachasodium/, Hacl_Symmetric_Chacha20_Sodium.ml Hacl_Test_Chacha20_Sodium.ml)  -o test_chachasodium.exe
	./test_chachasodium.exe

bla:
	gcc-5 -Wno-unused-but-set-variable -std=c11 -Wall -Werror -Wno-parentheses -Wno-unused-variable -g -O3 -fwrapv -I /home/jkz/dev/FStar/../kremlin/kremlib -I /home/jkz/dev/FStar/../kremlin/test -I /home/jkz/dev/kremlin/kremlib -I Hacl_Test_Chacha20_Sodium -I ../c -Wno-error=pointer-sign -Wno-error=incompatible-pointer-types -Wno-error=format= -D_GNU_SOURCE Hacl_Test_Chacha20_Sodium/Prims.c Hacl_Test_Chacha20_Sodium/FStar_Mul.c Hacl_Test_Chacha20_Sodium/FStar_Squash.c Hacl_Test_Chacha20_Sodium/FStar_StrongExcludedMiddle.c Hacl_Test_Chacha20_Sodium/FStar_List_Tot.c Hacl_Test_Chacha20_Sodium/FStar_Classical.c Hacl_Test_Chacha20_Sodium/FStar_ListProperties.c Hacl_Test_Chacha20_Sodium/FStar_SeqProperties.c Hacl_Test_Chacha20_Sodium/FStar_Math_Lemmas.c Hacl_Test_Chacha20_Sodium/FStar_BitVector.c Hacl_Test_Chacha20_Sodium/FStar_UInt.c Hacl_Test_Chacha20_Sodium/FStar_Int.c Hacl_Test_Chacha20_Sodium/FStar_FunctionalExtensionality.c Hacl_Test_Chacha20_Sodium/FStar_PropositionalExtensionality.c Hacl_Test_Chacha20_Sodium/FStar_PredicateExtensionality.c Hacl_Test_Chacha20_Sodium/FStar_TSet.c Hacl_Test_Chacha20_Sodium/FStar_Set.c Hacl_Test_Chacha20_Sodium/FStar_Map.c Hacl_Test_Chacha20_Sodium/FStar_Ghost.c Hacl_Test_Chacha20_Sodium/FStar_All.c Hacl_Test_Chacha20_Sodium/Hacl_UInt64.c Hacl_Test_Chacha20_Sodium/Hacl_UInt128.c Hacl_Test_Chacha20_Sodium/Hacl_UInt32.c Hacl_Test_Chacha20_Sodium/Hacl_UInt8.c Hacl_Test_Chacha20_Sodium/Hacl_Cast.c Hacl_Test_Chacha20_Sodium/FStar_Buffer.c  Hacl_Test_Chacha20_Sodium/Hacl_Symmetric_Chacha20_Sodium.c  ../../kremlin/kremlib/kremlib.c ../../kremlin/test/testlib.c bla.c  -o blah.exe -lsodium -m32
