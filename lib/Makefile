FSTAR_HOME ?= ../../FStar
HACL_HOME  ?= ..

CACHE_DIR = .cache
HINT_DIR  = .hints

include ../Makefile.include

.PHONY: all verify clean

all:
	rm -f .depend && $(MAKE) .depend
	$(MAKE) verify

FSTAR_INCLUDE_DIRS = \
  $(KREMLIN_HOME)/kremlib \
  $(HACL_HOME)/lib \
  $(HACL_HOME)/lib/fst

FSTAR_FLAGS = $(OTHERFLAGS) --cmi \
  --cache_checked_modules --cache_dir $(CACHE_DIR) \
  $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS)

ENABLE_HINTS = --use_hints --use_hint_hashes --record_hints --query_stats

ROOTS = $(addprefix fst/, \
	Lib.IntTypes.fst \
	Lib.RawIntTypes.fst \
	Lib.Sequence.fst \
	Lib.ByteSequence.fst \
	Lib.ByteBuffer.fst \
	Lib.Buffer.fst \
	Lib.LoopCombinators.fst \
	Lib.PrintSequence.fst \
	Lib.NatMod.fst) \
	c/Lib.Loops.fst

FIXME = fst/Lib.IntVector.fst

.depend:
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar' > $@

include .depend

$(HINT_DIR):
	mkdir -p $@

# Admit SMT queries for modules in the FStar namespace and prims
$(CACHE_DIR)/FStar.%.checked $(CACHE_DIR)/prims.%.checked: | .depend
	$(FSTAR) $< --admit_smt_queries true && \
	touch $@

$(CACHE_DIR)/%.checked: | .depend $(HINT_DIR)
	$(FSTAR) $< $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $<).hints && \
	touch $@

verify: $(addsuffix .checked, $(addprefix $(CACHE_DIR)/,$(notdir $(ROOTS))))

# Targets for interactive mode

%.fst-in:
	@echo $(FSTAR_FLAGS) \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fst.hints

%.fsti-in:
	@echo $(FSTAR_FLAGS) \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fsti.hints

# Clean targets

SHELL=/bin/bash

clean:
	rm -rf $(CACHE_DIR)
