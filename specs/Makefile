FSTAR_HOME ?= ../../FStar
HACL_HOME  ?= ..

CACHE_DIR     ?= $(HACL_HOME)/.cache
HINT_DIR      ?= $(HACL_HOME)/.hints

include ../Makefile.include

.PHONY: all verify clean

all:
	rm -f .depend && $(MAKE) .depend
	$(MAKE) verify

FSTAR_INCLUDE_DIRS = \
  $(KREMLIN_HOME)/kremlib \
  $(HACL_HOME)/lib \
  $(HACL_HOME)/specs \
  $(HACL_HOME)/specs/lemmas

FSTAR_FLAGS = --cmi \
  --cache_checked_modules --cache_dir $(CACHE_DIR) \
  --already_cached "'Prims+FStar+LowStar+C+Spec.Loops+TestLib'" \
  $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS) $(OTHERFLAGS)

ENABLE_HINTS = --use_hints --use_hint_hashes --record_hints --query_stats

ALL_SOURCES = $(wildcard *.fst) $(wildcard *.fsti)

FIXME = \
	Spec.HPKE.fst \
	Spec.HPKE.CFRG.fst \
	Spec.Poly1305.Generic.fst \
	Spec.Hash.KeyedHash.fst \
	Spec.Hash.KeyedHash.fsti \
	Spec.HMAC.KeyedHash.fst \
	Spec.HMAC.KeyedHash.fsti \
	Spec.Blake2.Incremental.fst

ROOTS = $(filter-out $(FIXME),$(ALL_SOURCES))

.depend:
	$(info $(ROOTS))
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -LowStar -FStar +FStar.Kremlin.Endianness -Lib.IntVector' > $@

include .depend

$(HINT_DIR):
	mkdir -p $@

$(CACHE_DIR):
	mkdir -p $@

$(CACHE_DIR)/%.checked: | .depend $(HINT_DIR) $(CACHE_DIR)
	$(FSTAR) $< $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $*).hints && \
	touch -c $@

verify: $(addsuffix .checked, $(addprefix $(CACHE_DIR)/,$(ROOTS)))

test:
	$(MAKE) -f Makefile.test

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
	rm -rf *.checked *~
	rm -rf *.cmi *.cmo *.cmx *.o *~ *.out *.exe *-ml

distclean: clean
