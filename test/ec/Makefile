all: test-kremlin test-ocaml

FSTAR_HOME?=../../../FStar
KREMLIN_HOME?=../../../kremlin
HACL_HOME?=../..
include $(HACL_HOME)/lib/hyperstack/Makefile.include
KREMLIN_INCLUDES=$(addprefix -I , $(HACL_KREMLIN) $(HACL_EC) . $(KREMTEST)) \
	$(KREMTEST)/testlib.c -add-include \"testlib.h\"
OCAML_INCLUDES=$(addprefix -I , $(HACL_LIB) $(HACL_EC) $(OCAML_LIB))

TEST_CURVE25519=Hacl.Test.Curve25519 Hacl.Test.Curve25519_donna_c64
TESTS=$(TEST_CURVE25519)

.PHONY:test-kremlin test-ocaml

test-kremlin: $(addsuffix -krml, $(TESTS))
test-ocaml: #curve25519-test
%-krml: %.fst
	mkdir -p $(subst .,_,$(basename $^))
	$(KREMLIN) $(KREMLIN_ARGS) $(KREMLIN_INCLUDES) -no-prefix $(basename $^) $^ \
		 -warn-error -1-2-3-4-5-6 \
		-tmpdir $(subst .,_,$(basename $^)) -o $(subst .,_,$(basename $^)).exe
	./$(subst .,_,$(basename $^)).exe

clean:
	make -C $(FSTAR_HOME)/ulib/ml clean
	make -C $(HACL_LIB) clean
	rm -rf *.c *.h *.out *.cmx *.o *.cmi *~ *.cmo *.exe *.krml \
		$(subst .,_,$(TESTS))
	rm -f $(addprefix ./ml/, *~ *.o *.cmx *.cmi *.cmo)
	rm -rf $(CURVE25519_ODIR)

# OCaml HST variables
REALIZED_MLI_HST=Hacl_UInt8 Hacl_UInt32 Hacl_UInt64 Hacl_UInt128
REALIZED_HST=Hacl_Cast Hacl_SBuffer 
REALIZED_MODULE_HST=$(subst _,., $(REALIZED_HST))
REALIZED_ML_HST=$(addsuffix .mli,$(REALIZED_MLI_HST)) $(addsuffix .ml,$(REALIZED_MLI_HST) $(REALIZED_HST))
NO_CODEGEN_HST=$(addprefix --no_extract , $(REALIZED_MODULE_HST))

CURVE25519_ODIR=curve25519
# Extracted OCaml HST files
CURVE_EXTRACTED_HST=FStar_FunctionalExtensionality.ml FStar_TSet.ml FStar_List_Tot.ml FStar_Seq.ml FStar_Ghost.ml FStar_Math_Lib.ml Math_Lemmas.ml Math_Definitions.ml Math_Field.ml Math_Curve.ml Curve_Parameters.ml Curve_Bigint.ml Curve_Fsum.ml Curve_FsumWide.ml Curve_Fdifference.ml Curve_Fscalar.ml Curve_Fproduct.ml Curve_Modulo.ml Curve_Bignum.ml Curve_Crecip.ml Curve_Point.ml Curve_AddAndDouble.ml Curve_Ladder.ml

CURVE25519_FSTAR=Hacl.EC.Curve25519.fst
CURVE25519_EXTRACTED=FStar_FunctionalExtensionality.ml FStar_TSet.ml FStar_List_Tot.ml FStar_Seq.ml FStar_Ghost.ml FStar_Math_Lib.ml \
	Hacl_EC_Curve25519_Parameters.ml \
	Hacl_EC_Curve25519_Bigint.ml \
	Hacl_EC_Curve25519_Utils.ml \
	Hacl_EC_Curve25519_Bignum_Fsum.ml \
	Hacl_EC_Curve25519_Bignum_Fscalar.ml \
	Hacl_EC_Curve25519_Bignum_Fdifference.ml \
	Hacl_EC_Curve25519_Bignum_Fproduct.ml \
	Hacl_EC_Curve25519_Bignum_Modulo_Lemmas.ml \
	Hacl_EC_Curve25519_Bignum_Modulo.ml \
	Hacl_EC_Curve25519_Bignum.ml \
	Hacl_EC_Curve25519_PPoint.ml \
	Hacl_EC_Curve25519_AddAndDouble.ml \
	Hacl_EC_Curve25519_Ladder.ml \
	Hacl_EC_Curve25519_Crecip.ml \
	Hacl_EC_Curve25519.ml

# Curve25519 extraction to OCaml
curve25519-extract: ml-lib
	@mkdir -p $(CURVE25519_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OCAML_OPTIONS) $(CURVE25519_FSTAR) \
		$(OCAML_INCLUDES) -tmpdir $(CURVE25519_ODIR)
	@sed -i 's/(Obj.magic ((fun pp ppq p pq q n ctr b scalar/(((fun pp ppq p pq q n ctr b scalar/g' $(CURVE25519_ODIR)/Hacl_EC_Curve25519_Ladder.ml

curve25519-compile: curve25519-extract
	$(OCAMLOPT) -I $(HACL_LIB)/ml -I $(CURVE25519_ODIR) \
		$(addprefix $(HACL_LIB)/ml/,$(REALIZED_ML_HST)) \
	  	$(addprefix $(CURVE25519_ODIR)/,$(CURVE25519_EXTRACTED)) \
		ml/test_curve25519_hst.ml -o test_curve25519.exe

curve25519-test: curve25519-compile
	./test_curve25519.exe


OLD_FILES=Hacl_Test_Curve25519/Prims.c \
	Hacl_Test_Curve25519/FStar_Mul.c \
	Hacl_Test_Curve25519/FStar_Squash.c \
	Hacl_Test_Curve25519/FStar_StrongExcludedMiddle.c \
	Hacl_Test_Curve25519/FStar_List_Tot.c \
	Hacl_Test_Curve25519/FStar_Classical.c \
	Hacl_Test_Curve25519/FStar_ListProperties.c \
	Hacl_Test_Curve25519/FStar_SeqProperties.c \
	Hacl_Test_Curve25519/FStar_Math_Lemmas.c \
	Hacl_Test_Curve25519/FStar_BitVector.c \
	Hacl_Test_Curve25519/FStar_UInt.c \
	Hacl_Test_Curve25519/FStar_FunctionalExtensionality.c \
	Hacl_Test_Curve25519/FStar_PropositionalExtensionality.c \
	Hacl_Test_Curve25519/FStar_PredicateExtensionality.c \
	Hacl_Test_Curve25519/FStar_TSet.c \
	Hacl_Test_Curve25519/FStar_Set.c \
	Hacl_Test_Curve25519/FStar_Map.c \
	Hacl_Test_Curve25519/FStar_Ghost.c \
	Hacl_Test_Curve25519/FStar_All.c \
	Hacl_Test_Curve25519/Hacl_UInt64.c \
	Hacl_Test_Curve25519/Hacl_UInt128.c \
	Hacl_Test_Curve25519/Hacl_UInt32.c \
	Hacl_Test_Curve25519/Hacl_UInt8.c \
	Hacl_Test_Curve25519/FStar_Int.c \
	Hacl_Test_Curve25519/Hacl_Cast.c \
	Hacl_Test_Curve25519/FStar_Buffer.c \
	Hacl_Test_Curve25519/FStar_Buffer_Quantifiers.c \
	Hacl_Test_Curve25519/Hacl_EC_Curve25519_Parameters.c \
	Hacl_Test_Curve25519/Hacl_EC_Curve25519_Bigint.c \
	Hacl_Test_Curve25519/Hacl_EC_Curve25519_Utils.c \
	Hacl_Test_Curve25519/Hacl_EC_Curve25519_Bignum_Fproduct.c \
	Hacl_Test_Curve25519/Hacl_EC_Curve25519_Bignum_Fscalar.c \
	Hacl_Test_Curve25519/Hacl_EC_Curve25519_Bignum_Fdifference.c \
	Hacl_Test_Curve25519/Hacl_EC_Curve25519_Bignum_Fsum.c \
	Hacl_Test_Curve25519/Hacl_EC_Curve25519_Bignum_Modulo.c \
	Hacl_Test_Curve25519/Hacl_EC_Curve25519_Bignum.c \
	Hacl_Test_Curve25519/Hacl_EC_Curve25519_PPoint.c \
	Hacl_Test_Curve25519/Hacl_EC_Curve25519_AddAndDouble.c \
	Hacl_Test_Curve25519/Hacl_EC_Curve25519_Ladder.c \
	Hacl_Test_Curve25519/Hacl_EC_Curve25519_Crecip.c \
	Hacl_Test_Curve25519/Hacl_EC_Curve25519.c \
	Hacl_Test_Curve25519/Hacl_Test_Curve25519.c \
	/home/jkz/dev/kremlin/kremlib/kremlib.c \
	../../../kremlin/test/testlib.c


FILES=Hacl_Test_Curve25519_donna_c64/Prims.c \
	Hacl_Test_Curve25519_donna_c64/FStar_Mul.c \
	Hacl_Test_Curve25519_donna_c64/FStar_Squash.c \
	Hacl_Test_Curve25519_donna_c64/FStar_StrongExcludedMiddle.c \
	Hacl_Test_Curve25519_donna_c64/FStar_List_Tot.c \
	Hacl_Test_Curve25519_donna_c64/FStar_Classical.c \
	Hacl_Test_Curve25519_donna_c64/FStar_ListProperties.c \
	Hacl_Test_Curve25519_donna_c64/FStar_SeqProperties.c \
	Hacl_Test_Curve25519_donna_c64/FStar_Math_Lemmas.c \
	Hacl_Test_Curve25519_donna_c64/FStar_BitVector.c \
	Hacl_Test_Curve25519_donna_c64/FStar_UInt.c \
	Hacl_Test_Curve25519_donna_c64/FStar_Int.c \
	Hacl_Test_Curve25519_donna_c64/FStar_FunctionalExtensionality.c \
	Hacl_Test_Curve25519_donna_c64/FStar_PropositionalExtensionality.c \
	Hacl_Test_Curve25519_donna_c64/FStar_PredicateExtensionality.c \
	Hacl_Test_Curve25519_donna_c64/FStar_TSet.c \
	Hacl_Test_Curve25519_donna_c64/FStar_Set.c \
	Hacl_Test_Curve25519_donna_c64/FStar_Map.c \
	Hacl_Test_Curve25519_donna_c64/FStar_Ghost.c \
	Hacl_Test_Curve25519_donna_c64/FStar_All.c \
	Hacl_Test_Curve25519_donna_c64/Hacl_UInt64.c \
	Hacl_Test_Curve25519_donna_c64/Hacl_UInt128.c \
	Hacl_Test_Curve25519_donna_c64/Hacl_UInt32.c \
	Hacl_Test_Curve25519_donna_c64/Hacl_UInt8.c \
	Hacl_Test_Curve25519_donna_c64/Hacl_Cast.c \
	Hacl_Test_Curve25519_donna_c64/FStar_Buffer.c \
	Hacl_Test_Curve25519_donna_c64/Hacl_EC_Curve25519_donna_c64_Fsum.c \
	Hacl_Test_Curve25519_donna_c64/Hacl_EC_Curve25519_donna_c64_Fscalar.c \
	Hacl_Test_Curve25519_donna_c64/Hacl_EC_Curve25519_donna_c64_Fmul.c \
	Hacl_Test_Curve25519_donna_c64/Hacl_EC_Curve25519_donna_c64.c \
	Hacl_Test_Curve25519_donna_c64/Hacl_Test_Curve25519_donna_c64.c \
	/home/jkz/dev/kremlin/kremlib/kremlib.c \
	../../../kremlin/test/testlib.c


old_test:
	gcc -Ofast -m64 -march=native -funroll-loops -flto $(OLD_FILES) -I $(KREMLIN_HOME)/kremlib -I $(KREMLIN_HOME)/test -o test_old.exe
	./test_old.exe

donna_test:
	gcc -Ofast -m64 -march=native -funroll-loops -flto $(FILES) -I $(KREMLIN_HOME)/kremlib -I $(KREMLIN_HOME)/test -o test_donna.exe
	./test_donna.exe
