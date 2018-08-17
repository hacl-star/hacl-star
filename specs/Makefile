include ../Makefile.include

OUTPUT_DIR = extracted

FSTAR += --record_hints --odir $(OUTPUT_DIR) --cache_checked_modules

# TODO: move the specification tests to their own files so that we don't pollute
# the specs with huge definitions in the scope
#
# NOTE: we assume every single one of these files defines a function named test,
# of type unit -> bool -- this Makefile will auto-generate test drivers  based
# on that assumption
ROOTS=Spec.GF128.fst Spec.Poly1305.fst Spec.Curve25519.fst Spec.Chacha20.fst \
  Spec.Salsa20.fst Spec.Chacha20Poly1305.fst $(wildcard Spec.*.Test.fst) \
  Spec.Ed25519.fst

# TODO: decide what to do with the following (excluded) specs:
#  Spec.HMAC.SHA2_256.fst Spec.HMAC.SHA2_384.fst Spec.HMAC.SHA2_512.fst

# Always generate the dependency file
.PHONY: .depend
.PRECIOUS: .depend
.depend:
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar +FStar.Endianness' > $@

include .depend

ALL_CHECKED_FILES = $(addsuffix .checked,$(ROOTS))

%.checked:
	$(FSTAR) $< && \
	touch $@

$(OUTPUT_DIR)/%_AutoTest.ml:
	echo "if not ($*.test ()) then (print_endline \"$* failed\"; exit 1)" > $@

$(OUTPUT_DIR)/%.ml:
	$(FSTAR) $(subst .checked,,$<) --codegen OCaml --extract_module $(subst .fst.checked,,$(notdir $<))

all: $(ALL_CHECKED_FILES)

test: $(subst .,_,$(patsubst %.fst,test-%,$(ROOTS)))

test-%: $(OUTPUT_DIR)/%_AutoTest.exe
	$<

OCAMLOPT += -I $(OUTPUT_DIR) -I $(HACL_KREMLIN)

# Can't be super subtle here... because the F* dependency analysis doesn't give
# us a way to name the cmx dependencies of a given module
ALL_CMX_FILES = $(patsubst %.ml,%.cmx,$(shell echo $(ALL_ML_FILES) | tail -r))

$(OUTPUT_DIR)/%_AutoTest.exe: $(ALL_CMX_FILES) $(OUTPUT_DIR)/%_AutoTest.ml
	$(OCAMLOPT) $^ -o $@

%.cmx: %.ml
	$(OCAMLOPT) -c $< -o $@

clean:
	rm -rf $(OUTPUT_DIR)
	rm -rf *.checked
