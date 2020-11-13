HACL_HOME = ../..

py-test: tests/Spec_Dilithium_Test.exe
	tests/Spec_Dilithium_Test.exe | python3 tests/testing.py


all: all-tests


FSTAR_ROOTS = Spec.Dilithium.Params.fst Spec.Dilithium.Poly.fst Spec.Dilithium.fst

include $(HACL_HOME)/Makefile.local

SPECS_DIR += $(HACL_HOME)/dilithium-spec $(HACL_HOME)/dilithium-spec/tests

ALL_HACL_SOURCE_DIRS = \
  $(LIB_DIR) $(SPECS_DIR) $(CODE_DIRS) $(VALE_DIRS) \
  $(EVERCRYPT_DIRS) $(MERKLE_DIRS) \
  $(KREMLIN_HOME)/runtime

ALL_HACL_DIRS	?= $(ALL_HACL_SOURCE_DIRS) $(HACL_HOME)/obj


# By default, we process all the files in the current directory. Here, we
# *extend* the set of relevant files with the tests.
FSTAR_ROOTS += tests/Spec.Dilithium.Test.fst #$(wildcard tests/*.fst) $(wildcard alternative/*.fst) $(wildcard experimental/*.fst)


ex:
	echo $(notdir $(FSTAR_ROOTS))



.PHONY: all-tests
all-tests: $(subst .,_,$(patsubst %.fst,test-ml-%,$(notdir $(wildcard tests/*.fst))))

.PRECIOUS: tests/%_AutoTest.ml
tests/%_AutoTest.ml:
	echo "if not ($*.test ()) then (print_endline \"$* failed\"; exit 1)" > $@

%.exe:

.PRECIOUS: tests/%.exe
tests/%.exe: $(ALL_CMX_FILES) tests/%_AutoTest.ml
	$(OCAMLOPT) $^ -o $@

.PHONY: test-ml-%
test-ml-%: tests/%.exe
	$<
