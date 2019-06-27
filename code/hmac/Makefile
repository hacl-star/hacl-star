FSTAR_HOME   ?= ../../../../FStar
KREMLIN_HOME ?= ../../../../kremlin
HACL_HOME    = ../..

OUTPUT_DIR    = .output
HINT_DIR      = .hints
GENERATED_DIR = hmac-c
OUT_DIR	      = hmac-c

.PHONY: all test stage1 stage2 clean clean-c distclean

all: test

test:
	rm -f .depend && $(MAKE) .depend
	$(MAKE) stage1
	STAGE=2 $(MAKE) stage2

stage1: $(GENERATED_DIR)/Hacl_HMAC.c


FSTAR_INCLUDE_DIRS = \
  $(HACL_KREMLIN) \
  $(KREMLIN_HOME)/kremlib \
  $(HACL_HOME)/specs \
  $(HACL_HOME)/specs/lemmas \
  $(HACL_HOME)/code/hash \
  $(HACL_HOME)/lib


FSTAR_FLAGS = $(OTHERFLAGS) --cmi \
  --cache_checked_modules --odir $(OUTPUT_DIR) \
  --already_cached "'Prims+FStar+LowStar+C+Spec.Loops+TestLib+Lib'" \
  $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS)

ENABLE_HINTS = --use_hints --use_hint_hashes --record_hints --query_stats

ROOTS = Hacl.HMAC.fst

.PRECIOUS: %.krml

.depend:
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar -LowStar -Spec' > $@

include .depend


$(HINT_DIR):
	mkdir -p $@

%.checked: | .depend $(HINT_DIR)
	$(FSTAR) $< $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $*).hints && \
	touch -c $@

$(OUTPUT_DIR)/%.krml: | .depend
	$(FSTAR) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

# 2. Generation of .c files

KREMLIN_TESTLIB=-fbuiltin-uint128 -fnocompound-literals -fc89-scope -fparentheses -fcurly-braces \
	-funroll-loops 8 -warn-error +9 -add-include '"kremlib.h"' -add-include '"FStar_UInt_8_16_32_64.h"' $(KREMLIB)/dist/minimal/testlib.c

KREMLIN=$(KREMLIN_HOME)/krml

# 2. Generation of .c files

# We use -drop (deprecated) only to avoid creating unnecessary .c,.h files
$(GENERATED_DIR)/Hacl_Hash_SHA2.c: $(ALL_KRML_FILES) | .depend
	$(KREMLIN) $(KREMLIN_TESTLIB) -skip-compilation  \
	-library 'C,FStar' \
	-bundle 'Lib.*' \
	-bundle 'Spec.*' \
	-bundle 'C=C.Endianness' \
	-drop 'FStar.UInt128,LowStar,Spec,Prims,Lib,C.Loops.*,Hacl.Spec.*,Hacl.Curve25519_64' \
	-tmpdir $(GENERATED_DIR) \
	$^


# 5. Targets for interactive mode

%.fst-in:
	@echo $(FSTAR_FLAGS) \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fst.hints

%.fsti-in:
	@echo $(FSTAR_FLAGS) \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fsti.hints

# 6. Clean targets

SHELL=/bin/bash

clean:
	rm -rf $(GENERATED_DIR) $(OUT_DIR)/*.exe $(OUT_DIR)/*.a
	rm -rf include/*.o include/*.d

clean-c:
	rm -rf $(GENERATED_DIR)/{*.{c,h},Makefile.include}

distclean: clean
	rm -rf $(OUT_DIR) $(OUTPUT_DIR) *.checked
