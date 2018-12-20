HACL_HOME = ../..
KREMLIN_HOME ?= ../../../kremlin

include ../Makefile.common

FSTAR_INCLUDES += $(HACL_HOME)/providers/.cache

EVERCRYPT_HOME ?= ..
MLCRYPTO_HOME ?= ../../../MLCrypto

HACL_CODE = ../../code

EXTRACT_DIR = extract
CACHE_DIR   = cache

UNAME = $(shell uname)

ifeq ($(OS),Windows_NT)
  ifeq ($(shell uname -o),Cygwin)
    EVERCRYPT_HOME_RUN := $(shell cygpath -u $(shell cygpath -m ${EVERCRYPT_HOME}))
    MLCRYPTO_HOME_RUN := $(shell cygpath -u $(shell cygpath -m ${MLCRYPTO_HOME}))
  else
    EVERCRYPT_HOME_RUN := $(EVERCRYPT_HOME)
    MLCRYPTO_HOME_RUN := $(MLCRYPTO_HOME)
  endif
  PREFIX = PATH="$(MLCRYPTO_HOME_RUN)/openssl:$(EVERCRYPT_HOME_RUN)/dist/compact:$(PATH)"
else ifeq ($(UNAME),Darwin)
  PREFIX = DYLD_LIBRARY_PATH=$(MLCRYPTO_HOME)/openssl:$(EVERCRYPT_HOME)/dist/compact:$(DYLD_LIBRARY_PATH)
else ifeq ($(UNAME),Linux)
  PREFIX = LD_LIBRARY_PATH=$(MLCRYPTO_HOME)/openssl:$(EVERCRYPT_HOME)/dist/compact:$(LD_LIBRARY_PATH)
endif

FSTAR=$(FSTAR_HOME)/bin/fstar.exe

all:
	rm -f .depend && $(MAKE) .depend
	$(MAKE) test

.PRECIOUS: %.krml %.checked

ROOTS=$(wildcard *.fst)

.depend:
	$(FSTAR) \
	  $(addprefix --include , $(FSTAR_INCLUDES)) \
	  --cache_dir $(CACHE_DIR) \
	  --odir $(EXTRACT_DIR) \
	  --dep full $(ROOTS) > .depend

include .depend

%.checked: | .depend
	$(FSTAR) \
	  --cache_checked_modules \
	  --already_cached "* -Test" \
	  --cache_dir $(CACHE_DIR) \
	  --use_hints --record_hints --use_hint_hashes \
	  $(addprefix --include , $(FSTAR_INCLUDES)) \
	  $< && \
	touch $@

$(EXTRACT_DIR)/%.krml:
	$(FSTAR) --codegen Kremlin \
	  --cache_checked_modules \
	  --cache_dir $(CACHE_DIR) \
	  $(addprefix --include , $(FSTAR_INCLUDES)) \
	  --odir $(EXTRACT_DIR) \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<))

# hacks.h defines monomorphized types for `option string` and `uint8_t * uint8_t`, which are
# needed by fstar_bytes.h, and then includes fstar_bytes.h only if EverCrypt.h has been
# loaded.
$(EXTRACT_DIR)/Test.c: $(ALL_KRML_FILES) | .depend
	krml $(KOPTS) $^ -tmpdir $(EXTRACT_DIR) -no-prefix Test \
	  -skip-compilation \
	  -add-include '"kremlin/internal/compat.h"' \
	  -add-include '"kremlib.h"' \
	  -minimal -bundle 'Test=*' \
	  -library 'EverCrypt,EverCrypt.*' \
	  -ccopt -g

test: $(EXTRACT_DIR)/Test.c
	$(MAKE) -C $(EXTRACT_DIR) Test.exe
	$(PREFIX) extract/Test.exe

clean:
	rm -rf .depend cache
	-@find $(EXTRACT_DIR) -type f -and -not -name Makefile -and -not -name .gitignore -and -not -name temp.h \
        | xargs rm -f

%.fst-in:
	@echo $(addprefix --include ,$(FSTAR_INCLUDES))
