EVERCRYPT_HOME ?= ../
KREMLIN_HOME   ?= ../../../kremlin

EXTRACT_DIR = extract
CACHE_DIR   = cache
INCLUDE_PATHS = \
	$(KREMLIN_HOME)/kremlib \
	 ../multiplexer

UNAME = $(shell uname)

ifeq ($(OS),Windows_NT)
  ifeq ($(shell uname -o),Cygwin)
    EVERCRYPT_HOME_RUN := $(shell cygpath -a -u ${EVERCRYPT_HOME})
    MLCRYPTO_HOME_RUN := $(shell cygpath -a -u ${MLCRYPTO_HOME})
  else
    EVERCRYPT_HOME_RUN := $(EVERCRYPT_HOME)
    MLCRYPTO_HOME_RUN := $(MLCRYPTO_HOME)
  endif
  PREFIX = PATH="$(MLCRYPTO_HOME)/openssl:$(EVERCRYPT_HOME)/out:$(PATH)"
else ifeq ($(UNAME),Darwin)
  PREFIX = DYLD_LIBRARY_PATH=$(MLCRYPTO_HOME)/openssl:$(EVERCRYPT_HOME)/out:$(DYLD_LIBRARY_PATH)
else ifeq ($(UNAME),Linux)
  PREFIX = LD_LIBRARY_PATH=$(MLCRYPTO_HOME)/openssl:$(EVERCRYPT_HOME)/out:$(LD_LIBRARY_PATH)
endif

all: test

.depend:
	fstar.exe \
	  $(addprefix --include , $(INCLUDE_PATHS)) \
	  --cache_dir $(CACHE_DIR) \
	  --odir $(EXTRACT_DIR) \
	  --dep full Test.fst > .depend 

include .depend

%.checked: | .depend
	fstar.exe \
	  --cache_checked_modules \
	  --cache_dir $(CACHE_DIR) \
	  --admit_smt_queries true \
	  $(addprefix --include , $(INCLUDE_PATHS)) \
	  $<

$(EXTRACT_DIR)/%.krml:
	fstar.exe --codegen Kremlin \
	  --cache_checked_modules \
	  --cache_dir $(CACHE_DIR) \
	  $(addprefix --include , $(INCLUDE_PATHS)) \
	  --odir $(EXTRACT_DIR) \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(subst $(CACHE_DIR)/,,$(subst .checked,,$<))

# hacks.h defines monomorphized types for `option string` and `uint8_t * uint8_t`, which are
# needed by fstar_bytes.h, and then includes fstar_bytes.h only if EverCrypt.h has been
# loaded.
$(EXTRACT_DIR)/Test.c: $(filter-out $(EXTRACT_DIR)/prims.krml ,$(ALL_KRML_FILES)) | .depend
	krml $^ -tmpdir $(EXTRACT_DIR) -no-prefix Test \
	  -skip-compilation \
	  -drop FStar.Bytes \
	  -drop LowStar \
	  -bundle EverCrypt=EverCrypt.* \
	  -add-include '"kremlin/testlib.h"' \
	  -add-include '"kremlin/prims_int.h"' \
	  -add-include '"kremlin/prims_string.h"' \
	  -add-include '"kremlin/c_string.h"' \
	  -add-include '"hacks.h"'

test: $(EXTRACT_DIR)/Test.c
	$(MAKE) -C $(EXTRACT_DIR) test.exe
	$(PREFIX) extract/test.exe

clean:
	rm -rf .depend cache
	-@find $(EXTRACT_DIR) -type f -and -not -name Makefile -and -not -name .gitignore -and -not -name hacks.h \
        | xargs rm -f

%.fst-in:
	@echo --include ../multiplexer --include $(KREMLIN_HOME)/kremlib
