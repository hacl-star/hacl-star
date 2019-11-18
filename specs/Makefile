HACL_HOME = ..

all: all-tests

include ../Makefile.local

# By default, we process all the files in the current directory. Here, we
# *extend* the set of relevant files with the tests.
FSTAR_ROOTS += $(wildcard tests/*.fst) $(wildcard alternative/*.fst) $(wildcard experimental/*.fst)

.PHONY: all-tests
all-tests: $(subst .,_,$(patsubst %.fst,test-ml-%,$(notdir $(wildcard tests/*.fst))))

.PRECIOUS: specs/tests/%_AutoTest.ml
specs/tests/%_AutoTest.ml:
	echo "if not ($*.test ()) then (print_endline \"$* failed\"; exit 1)" > $@

.PRECIOUS: specs/tests/%.exe
specs/tests/%.exe: $(ALL_CMX_FILES) specs/tests/%_AutoTest.ml
	$(OCAMLOPT) $^ -o $@

.PHONY: test-ml-%
test-ml-%: specs/tests/%.exe
	$<
