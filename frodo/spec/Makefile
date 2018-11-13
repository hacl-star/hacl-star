FSTAR_HOME ?= ../../../FStar
HACL_HOME  ?= ../..

VARIANT    ?= 64-cSHAKE

ifeq ($(VARIANT),64-cSHAKE)
  TARGET = test
else ifeq ($(VARIANT),64-AES)
  TARGET = test
else ifeq ($(VARIANT),640-cSHAKE)
  TARGET = verify
else ifeq ($(VARIANT),976-cSHAKE)
  TARGET = verify
else ifeq ($(VARIANT),640-AES)
  TARGET = verify
else ifeq ($(VARIANT),976-AES)
  TARGET = verify
else
  $(error ERROR: VARIANT must be one of 64-cSHAKE, 640-cSHAKE, 976-cSHAKE, 64-AES, 640-AES, 976-AES)
endif

CACHE_DIR = .cache.$(VARIANT)
HINT_DIR  = .hints.$(VARIANT)
OUT_DIR   = frodo-ml.$(VARIANT)

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
  $(HACL_HOME)/lib \
  $(HACL_HOME)/lib/fst

FSTAR_FLAGS = $(OTHERFLAGS) --cmi \
  --cache_checked_modules --cache_dir $(CACHE_DIR) --odir $(OUT_DIR) \
  $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS)

ENABLE_HINTS = --use_hints --use_hint_hashes --record_hints --query_stats

ifeq ($(VARIANT),64-cSHAKE)
  ROOTS = test-$(VARIANT)/Spec.Frodo.Test.fst
  FSTAR += --include test-$(VARIANT)
else ifeq ($(VARIANT),64-AES)
  ROOTS = test-$(VARIANT)/Spec.Frodo.Test.fst
  FSTAR += --include test-$(VARIANT)
else
  ROOTS = Frodo.KEM.fst
endif

.depend:
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar' > $@

include .depend

# Admit SMT queries for modules in the FStar and Lib namespaces, and prims
$(CACHE_DIR)/FStar.%.checked $(CACHE_DIR)/prims.%.checked $(CACHE_DIR)/Lib.%.checked: | .depend
	$(FSTAR) $< --admit_smt_queries true && \
	touch $@

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

$(OUT_DIR)/Spec_Frodo_Test.cmx:
	@echo 'let _ = test()' >> $(OUT_DIR)/Spec_Frodo_Test.ml
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
