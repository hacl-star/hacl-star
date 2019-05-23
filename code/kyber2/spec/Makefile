FSTAR_HOME ?= ../../../../FStar
HACL_HOME  ?= ../../..

VARIANT    ?= 512

ifeq ($(VARIANT),512)
  TARGET = test
else
  $(error ERROR: VARIANT must be one of 512)
endif

CACHE_DIR = .cache.$(VARIANT)
HINT_DIR  = .hints.$(VARIANT)
OUT_DIR   = kyber2-ml.$(VARIANT)

include $(HACL_HOME)/Makefile.include

.PHONY: all verify test clean distclean

all:
	rm -f .depend && $(MAKE) .depend
	$(MAKE) $(TARGET)

verify: $(addprefix $(CACHE_DIR)/,Spec.Frodo.KEM.KeyGen.fst.checked Spec.Frodo.KEM.Encaps.fst.checked Spec.Frodo.KEM.Decaps.fst.checked)
	@echo SUCCESS!

# 1. Generation of .ml files
# - generate the F* dependency graph via `fstar --dep full`
# - verify every F* file in parallel to generate .checked files
# - extract each .checked file into a .ml file in parallel

FSTAR_INCLUDE_DIRS = \
  params-$(VARIANT) \
  $(HACL_HOME)/specs \
  $(HACL_HOME)/lib

FSTAR_FLAGS = $(OTHERFLAGS) --cmi \
  --cache_checked_modules --cache_dir $(CACHE_DIR) --odir $(OUT_DIR) \
  --already_cached "'Prims+FStar+LowStar+C+Spec.Loops+TestLib+Lib'" \
  $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS)

ENABLE_HINTS = --use_hints --use_hint_hashes --record_hints --query_stats

ifeq ($(VARIANT),512)
  ROOTS = Spec.Kyber2.Test.fst
  #FSTAR += --include test-$(VARIANT)
else
  ROOTS = Spec.Kyber2.Kem.fst
endif

.depend:
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar' > $@

include .depend

$(CACHE_DIR)/%.checked: | .depend
	$(FSTAR) $< $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $<).hints && \
	touch $@

$(OUT_DIR)/%.ml: | .depend
	$(FSTAR) --codegen OCaml \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

# 2. Compilation

$(OUT_DIR):
	mkdir -p $@

%.cmx:
	$(OCAMLOPT) -I $(OUT_DIR) -c $< -o $@

$(OUT_DIR)/Spec_Kyber2_Test.cmx:
	@echo 'let _ = test()' >> $(OUT_DIR)/Spec_Kyber2_Test.ml
	$(OCAMLOPT) -I $(OUT_DIR) -c $< -o $@

$(OUT_DIR)/test.exe: $(subst .ml,.cmx,$(ALL_ML_FILES)) | $(OUT_DIR)
	$(OCAMLOPT) -I $(OUT_DIR) -o $(OUT_DIR)/test.exe $(subst .ml,.cmx,$(ALL_ML_FILES))

test: $(OUT_DIR)/test.exe
	$(OUT_DIR)/test.exe

# 3. Targets for interactive mode

%.fst-in:
	@echo $(FSTAR_FLAGS) \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fst.hints

%.fsti-in:
	@echo $(FSTAR_FLAGS) \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fsti.hints

# 4. Clean targets

SHELL=/bin/bash

clean:
	rm -rf $(OUT_DIR)

distclean: clean
	rm -rf $(CACHE_DIR)
