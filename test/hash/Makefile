all: test-kremlin test-ocaml

FSTAR_HOME?=/opt/fstar
KREMLIN_HOME?=/opt/kremlin
HACL_HOME?=../..
include $(HACL_HOME)/lib/hyperstack/Makefile.include
KREMLIN_INCLUDES=$(addprefix -I , $(HACL_KREMLIN) $(HACL_CRYPTO_UTILS) $(HACL_HASH) . $(KREMTEST)) \
	$(KREMTEST)/testlib.c -add-include \"testlib.h\" $(HACL_LIB)/Math.Logic.Axioms.fst
OCAML_INCLUDES=$(addprefix --include , $(HACL_LIB) $(HACL_CRYPTO_UTILS) $(HACL_HASH) $(OCAML_LIB))

TEST_SHA2_L256=Hacl.Test.SHA2.L256
TESTS=$(TEST_SHA2_L256) 

.PHONY:test-kremlin

test-kremlin: $(addsuffix -krml, $(TESTS))
test-ocaml: sha2-test

%-krml: %.fst
	mkdir -p $(subst .,_,$(basename $^))
	$(KREMLIN) $(KREMLIN_ARGS) $(KREMLIN_INCLUDES) -no-prefix $(basename $^) $^ \
		 -warn-error -1-2-3-4-5-6 \
		-tmpdir $(subst .,_,$(basename $^)) -o $(subst .,_,$(basename $^)).exe
	./$(subst .,_,$(basename $^)).exe -verbose

clean:
	make -C $(HACL_LIB) clean
	rm -rf *.c *.h *.out *.cmx *.o *.cmi *~ *.cmo *.exe *.krml \
		$(subst .,_,$(TESTS)) $(CHACHA_ODIR)
	rm -f $(addprefix ./ml/, *~ *.o *.cmx *.cmi *.cmo)

# OCaml variables
REALIZED_MLI_HST=Hacl_UInt8 Hacl_UInt32 Hacl_UInt64 Hacl_UInt128
REALIZED_HST=Hacl_Cast Hacl_SBuffer
REALIZED_MODULE_HST=$(subst _,., $(REALIZED_HST))
REALIZED_ML_HST=$(addsuffix .mli,$(REALIZED_MLI_HST)) $(addsuffix .ml,$(REALIZED_MLI_HST) $(REALIZED_HST))
NO_CODEGEN_HST=$(addprefix --no_extract , $(REALIZED_MODULE_HST))

# FStar files
SHA2_L256_FSTAR_HST= $(addprefix $(HACL_CRYPTO_UTILS)/,Hacl.Conversions.fst Hacl.Operations.fst) $(addprefix $(HACL_HASH)/,Hacl.Hash.SHA2.L256.fst)
SHA2_L256_EXTRACTED_HST=Hacl_Conversions.ml Hacl_Operations.ml Hacl_Hash_SHA2_L256.ml

SHA2_L256_ODIR=sha2

#################
# OCAML TARGETS #
#################

# OCaml extracton of CHACHA20
sha2-l256-extract: ml-lib
	mkdir -p $(SHA2_L256_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OCAML_OPTIONS) $(OCAML_INCLUDES) $(SHA2_L256_FSTAR_HST) --odir $(SHA2_L256_ODIR)

sha2-l256-compile: sha2-l256-extract
	$(OCAMLOPT) -I $(HACL_LIB)/ml -I $(SHA2_L256_ODIR) \
	  $(addprefix $(HACL_LIB)/ml/,$(REALIZED_ML_HST)) \
	  $(addprefix $(SHA2_L256_ODIR)/,$(SHA2_L256_EXTRACTED_HST)) ml/test_sha2_l256.ml -o test_sha2_l256.exe

sha2-l256-test: sha2-l256-compile
	./test_sha2_l256.exe
