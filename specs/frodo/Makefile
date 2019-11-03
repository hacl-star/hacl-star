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

CACHE_DIR = $(HACL_HOME)/obj
HINT_DIR  = $(HACL_HOME)/hints
OUT_DIR   = $(HACL_HOME)/obj

include $(HACL_HOME)/Makefile.include

.PHONY: all verify test clean distclean

all:
	rm -f .depend && $(MAKE) .depend
	$(MAKE) $(TARGET)

verify: $(addprefix $(CACHE_DIR)/,Spec.Frodo.KEM.checked)
	@echo SUCCESS!

# 1. Generation of .ml files
# - generate the F* dependency graph via `fstar --dep full`
# - verify every F* file in parallel to generate .checked files
# - extract each .checked file into a .ml file in parallel

FSTAR_INCLUDE_DIRS = \
  params-$(VARIANT) \
  $(HACL_HOME)/specs \
  $(HACL_HOME)/lib \
  $(HACL_HOME)/obj

FSTAR_FLAGS = $(OTHERFLAGS) --cmi \
  --cache_checked_modules --cache_dir $(CACHE_DIR) --odir $(OUT_DIR) \
  --already_cached "'Prims FStar LowStar C Spec.Loops TestLib Lib'" \
  $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS)

ENABLE_HINTS = --use_hints --use_hint_hashes --record_hints --query_stats

ifeq ($(VARIANT),64-cSHAKE)
  ROOTS = test-$(VARIANT)/Spec.Frodo.Test.fst
  FSTAR += --include test-$(VARIANT)
else ifeq ($(VARIANT),64-AES)
  ROOTS = test-$(VARIANT)/Spec.Frodo.Test.fst
  FSTAR += --include test-$(VARIANT)
endif

ROOTS += Spec.Frodo.KEM.fst

.depend:
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar' > $@

include .depend

$(CACHE_DIR)/%.checked: | .depend $(CACHE_DIR)
	$(FSTAR) $< $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $<).hints && \
	touch $@

$(OUT_DIR)/%.ml: | .depend
	$(FSTAR) --codegen OCaml \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

# 2. Compilation

ifeq ($(OS),Windows_NT)
  export OCAMLPATH := $(FSTAR_HOME)/bin;$(OCAMLPATH)
else
  export OCAMLPATH := $(FSTAR_HOME)/bin:$(OCAMLPATH)
endif

OCAMLOPT = ocamlfind opt -package fstarlib -linkpkg -g -w -8-20-26

%.cmx:
	$(OCAMLOPT) -I $(OUT_DIR) -c $< -o $@

$(OUT_DIR)/Spec_Frodo_Test.cmx:
	@echo -e '\nlet _ = test()' >> $(OUT_DIR)/Spec_Frodo_Test.ml
	$(OCAMLOPT) -I $(OUT_DIR) -c $< -o $@

$(OUT_DIR)/test.exe: $(subst .ml,.cmx,$(ALL_ML_FILES)) | $(OUT_DIR)
	$(OCAMLOPT) -I $(OUT_DIR) -o $(OUT_DIR)/test.exe $(subst .ml,.cmx,$(ALL_ML_FILES))

test: $(OUT_DIR)/test.exe
	$(OUT_DIR)/test.exe

# 3. Targets for interactive mode

%.fst-in:
	@echo $(addprefix --include ,$(FSTAR_INCLUDE_DIRS)) \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fst.hints

%.fsti-in:
	@echo $(addprefix --include ,$(FSTAR_INCLUDE_DIRS)) \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fsti.hints
