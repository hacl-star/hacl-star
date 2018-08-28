all: verify extract test

# Old targets, backwards-compat:
.PHONY: old-%
old-%:
	$(MAKE) -f Makefile.old $*

# 0. Paths and includes

include Makefile.common

ROOTS=$(HACL_HOME)/code/hash-new/Hacl.SHA2.fst

ALL_CHECKED_FILES = $(addsuffix .checked,$(ROOTS))

.PHONY: .depend
.depend:
	@$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar +FStar.Endianness +FStar.Kremlin.Endianness' > $@

include .depend

# 1. Top-level entry points for this Makefile

verify: $(ALL_CHECKED_FILES)

extract: # $(OUTPUT_DIR)/Makefile.include

# Backwards compat target name
extract-c: extract old-extract-c

clean: clean-c
	find $(DIRS) -iname '*.checked' | xargs rm -rf

clean-c: old-clean-c
	rm -rf $(OUTPUT_DIR)

test:

# 2. Verification

%.checked:
	$(FSTAR) $< && \
	touch $@

# 3. Extraction

.PRECIOUS: %.krml

$(OUTPUT_DIR)/%.krml:
	$(FSTAR) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

$(OUTPUT_DIR)/Makefile.include: $(ALL_KRML_FILES)
	$(KRML) -tmpdir $(OUTPUT_DIR) -skip-compilation -bundle Spec.* $^ \
	  -warn-error +9
