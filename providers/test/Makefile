EVERCRYPT_HOME ?= ..
KREMLIN_HOME   ?= ../../../kremlin
MLCRYPTO_HOME ?= ../../../MLCrypto

HACL_CODE = ../../code

EXTRACT_DIR = extract
CACHE_DIR   = cache
INCLUDE_PATHS = \
  $(KREMLIN_HOME)/kremlib \
  ../evercrypt \
  $(HACL_CODE)/lib/kremlin \
  $(HACL_CODE)/curve25519/interfaces \
  $(HACL_CODE)/hash/interfaces \
  $(HACL_CODE)/api/interfaces \
  ../../specs

UNAME = $(shell uname)

ifeq ($(OS),Windows_NT)
  ifeq ($(shell uname -o),Cygwin)
    EVERCRYPT_HOME_RUN := $(shell cygpath -a -u ${EVERCRYPT_HOME})
    MLCRYPTO_HOME_RUN := $(shell cygpath -a -u ${MLCRYPTO_HOME})
  else
    EVERCRYPT_HOME_RUN := $(EVERCRYPT_HOME)
    MLCRYPTO_HOME_RUN := $(MLCRYPTO_HOME)
  endif
  PREFIX = PATH="$(MLCRYPTO_HOME_RUN)/openssl:$(EVERCRYPT_HOME_RUN)/out:$(PATH)"
else ifeq ($(UNAME),Darwin)
  PREFIX = DYLD_LIBRARY_PATH=$(MLCRYPTO_HOME)/openssl:$(EVERCRYPT_HOME)/out:$(DYLD_LIBRARY_PATH)
else ifeq ($(UNAME),Linux)
  PREFIX = LD_LIBRARY_PATH=$(MLCRYPTO_HOME)/openssl:$(EVERCRYPT_HOME)/out:$(LD_LIBRARY_PATH)
endif

FSTAR=$(FSTAR_HOME)/bin/fstar.exe

all:
	rm -f .depend && $(MAKE) .depend
	$(MAKE) test

.depend:
	$(FSTAR) \
	  $(addprefix --include , $(INCLUDE_PATHS)) \
	  --cache_dir $(CACHE_DIR) \
	  --odir $(EXTRACT_DIR) \
	  --dep full Test.fst Test.Bytes.fst > .depend 

include .depend

%.checked: | .depend
	$(FSTAR) \
	  --cache_checked_modules \
	  --admit_smt_queries true \
	  --cache_dir $(CACHE_DIR) \
	  $(addprefix --include , $(INCLUDE_PATHS)) \
	  $<

$(EXTRACT_DIR)/%.krml:
	$(FSTAR) --codegen Kremlin \
	  --cache_checked_modules \
	  --cache_dir $(CACHE_DIR) \
	  $(addprefix --include , $(INCLUDE_PATHS)) \
	  --odir $(EXTRACT_DIR) \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(subst $(CACHE_DIR)/,,$(subst .checked,,$<))

# hacks.h defines monomorphized types for `option string` and `uint8_t * uint8_t`, which are
# needed by fstar_bytes.h, and then includes fstar_bytes.h only if EverCrypt.h has been
# loaded.
$(EXTRACT_DIR)/Test.c: $(ALL_KRML_FILES) | .depend
	krml $^ -tmpdir $(EXTRACT_DIR) -no-prefix Test \
	  -skip-compilation \
	  -add-include '"kremlin/internal/compat.h"' \
	  -add-include '"temp.h"' \
	  -bundle 'Test=Test.*' \
	  -bundle 'C=C.*' \
	  -bundle 'LowStar.*' \
	  -bundle 'Hacl.Spec.*,Hacl.Spe.*,Spec.*' \
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
	@echo $(addprefix --include ,\
	  ../evercrypt $(KREMLIN_HOME)/kremlib \
          ../../code/lib/kremlin \
	  ../../specs \
	  ../../code/hash \
	  ../../code/hash/interfaces \
	  ../../code/curve25519 \
	  ../../code/curve25519/interfaces \
	  ../../code/bignum)
