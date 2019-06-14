FSTAR_HOME ?= ../../FStar
HACL_HOME  ?= ..

HINT_DIR  = .hints

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
  --cache_checked_modules \
  --already_cached "'Prims+FStar+LowStar+C+Spec.Loops+TestLib'" \
  $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS) $(OTHERFLAGS)

ENABLE_HINTS = --use_hints --use_hint_hashes --record_hints --query_stats

ALL_SOURCES = $(wildcard *.fst) $(wildcard *.fsti)

FIXME = \
	Spec.HPKE.fst \
	Spec.HPKE.CFRG.fst \
	Spec.RSAPSS.fst \
	Spec.Poly1305.Generic.fst \
	Spec.Hash_Generic.fst \
	Spec.Hash_Generic.fsti \
	Spec.HMAC_Generic.fst \
	Spec.HMAC_Generic.fsti

ROOTS = $(filter-out $(FIXME),$(ALL_SOURCES))

.depend:
	$(info $(ROOTS))
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -LowStar -FStar +FStar.Kremlin.Endianness -Lib.IntVector' > $@

include .depend

$(HINT_DIR):
	mkdir -p $@

%.checked: | .depend $(HINT_DIR)
	$(FSTAR) $< $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $*).hints && \
	touch -c $@

verify: $(addsuffix .checked, $(ROOTS))

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

distclean: clean
