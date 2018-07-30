FSTAR_HOME ?= ../../../FStar
HACL_HOME  ?= ../..

CACHE_DIR  = .cache
HINT_DIR   = .hints
OUT_DIR	   = frodo-ml

include $(HACL_HOME)/Makefile.include

all:
	rm -f .depend && $(MAKE) .depend
	$(MAKE) test

# 1. Generation of .ml files
# - generate the F* dependency graph via `fstar --dep full`
# - verify every F* file in parallel to generate .checked files
# - extract each .checked file into a .ml file in parallel

FSTAR_INCLUDE_DIRS = \
  $(HACL_HOME)/specs \
  $(HACL_HOME)/lib \
  $(HACL_HOME)/lib/fst

FSTAR_INCLUDES = $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(OTHERFLAGS) \
  --cache_checked_modules --cache_dir $(CACHE_DIR) \
  --odir $(OUT_DIR) $(FSTAR_INCLUDES)

ENABLE_HINTS = --use_hints --use_hint_hashes --record_hints --query_stats

%.fst-in:
	@echo \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fst.hints \
	  $(OTHERFLAGS) \
	  --cache_checked_modules --cache_dir $(CACHE_DIR) \
	  --odir $(OUT_DIR) $(FSTAR_INCLUDES)

ROOTS = Spec.Frodo.Test.fst

.depend:
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar' > $@

include .depend

# Admit SMT queries for modules in FStar namespace
$(CACHE_DIR)/FStar.%.fst.checked: | .depend
	$(FSTAR) --admit_smt_queries true $< && \
	touch $@

# We need this because F* can't take duplicate modules in the command line
$(CACHE_DIR)/Lib.IntTypes.fst.checked: | .depend
	$(FSTAR) $< \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $<).hints && \
	touch $@

$(CACHE_DIR)/Lib.IntTypes.fsti.checked: | .depend
	$(FSTAR) $< \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $<).hints && \
	touch $@

$(CACHE_DIR)/%.checked: | .depend
	$(FSTAR) $< \
	  --expose_interfaces $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $<).hints && \
	touch $@

# We need this because F* can't take duplicate modules in the command line
$(OUT_DIR)/Lib_IntTypes.ml: | .depend
	$(FSTAR) --codegen OCaml \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

$(OUT_DIR)/%.ml: | .depend
	$(FSTAR) --codegen OCaml \
	  --expose_interfaces $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

# 3. Compilation

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


# 4. Clean targets

SHELL=/bin/bash

.PHONY: clean
clean:
	rm -rf $(OUT_DIR)

.PHONY: distclean
distclean: clean
	rm -rf $(OUT_DIR) $(CACHE_DIR)
