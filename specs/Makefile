include $(FSTAR_HOME)/ulib/ml/Makefile.include

HACL_HOME ?= ..

OUTPUT_DIR = extracted

INCLUDES = $(KREMLIN_HOME)/kremlib $(HACL_HOME)/code/old/lib/kremlin old tests

FSTAR_INCLUDES = $(addprefix --include ,$(INCLUDES))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe --use_hints --record_hints \
  --odir $(OUTPUT_DIR) --cache_checked_modules $(FSTAR_INCLUDES) --cmi \
  --already_cached 'FStar LowStar C Spec.Loops -FStar.Endianness'

# NOTE: we assume every single one of these files defines a function named test,
# of type unit -> bool -- this Makefile will auto-generate test drivers based
# on that assumption
TEST_ROOTS=$(wildcard tests/*.fst)

OTHER_ROOTS=$(wildcard old/*.fst) $(wildcard *.fst) $(HACL_HOME)/code/old/lib/kremlin/FStar.Endianness.fst

ALL_CHECKED_FILES = $(addsuffix .checked,$(TEST_ROOTS) $(OTHER_ROOTS))

all: verify

verify: $(ALL_CHECKED_FILES)

# Always generate the dependency file
.depend:
	$(FSTAR) --dep full $(TEST_ROOTS) $(OTHER_ROOTS) --extract '* -Prims -FStar +FStar.Endianness +FStar.Kremlin.Endianness' > $@

include .depend

# Construction of checked and extracted files

%.fst-in:
	@echo $(FSTAR_INCLUDES)

%.checked:
	$(FSTAR) $< && \
	touch $@

$(OUTPUT_DIR)/%_AutoTest.ml:
	echo "if not ($*.test ()) then (print_endline \"$* failed\"; exit 1)" > $@

$(OUTPUT_DIR)/%.ml:
	$(FSTAR) $(subst .checked,,$<) --codegen OCaml --extract_module $(subst .fst.checked,,$(notdir $<))

test: $(subst .,_,$(patsubst %.fst,test-%,$(notdir $(TEST_ROOTS))))

test-%: $(OUTPUT_DIR)/%_AutoTest.exe
	$<

OCAMLOPT += -I $(OUTPUT_DIR) -I $(HACL_HOME)/code/lib/kremlin

TAC = $(shell which tac >/dev/null 2>&1 && echo "tac" || echo "tail -r")

# Can't be super subtle here... because the F* dependency analysis doesn't give
# us a way to name the cmx dependencies of a given module
ALL_CMX_FILES = $(patsubst %.ml,%.cmx,$(shell echo $(ALL_ML_FILES) | $(TAC)))

.PRECIOUS: $(OUTPUT_DIR)/%_AutoTest.exe
$(OUTPUT_DIR)/%_AutoTest.exe: $(ALL_CMX_FILES) $(OUTPUT_DIR)/%_AutoTest.ml
	$(OCAMLOPT) $^ -o $@

%.cmx: %.ml
	$(OCAMLOPT) -c $< -o $@

clean:
	rm -rf $(OUTPUT_DIR)
	rm -rf *.checked

.PHONY: all verify test clean
