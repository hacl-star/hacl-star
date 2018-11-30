include Makefile.common

ifeq ($(OS),Windows_NT)
  SO=dll
else
  SO=so
endif

# 1. Main entry points, along with some sanity checks

VALE_FSTI_HACK	= $(HACL_HOME)/vale/code/arch/x64/interop/fsti

all: $(VALE_FSTI_HACK) $(VALE_OBJ_DIR) $(HACL_CHECK) $(KREMLIB_CHECK)
	rm -f .depend && $(MAKE) .depend
	$(MAKE) all_

# Manual staging
all_: dist/compact/libevercrypt.$(SO) dist/compact/evercrypt.cmxa \
  dist/header/EverCrypt.h dist/coco/libevercrypt.$(SO)

# Temporary workaround: we want Vale to offer a relatively small dependency
# graph with just interfaces.
$(VALE_FSTI_HACK):
	mkdir -p $@
ifeq ($(OS),Windows_NT)
	cp $@/../*.fsti $@/
else
	ln -s $@/../*.fsti $@/
endif

$(VALE_OBJ_DIR):
	@echo "Please run scons --FSTAR-MY-VERSION --NO-VERIFY --EXTRACT-FSTAR in the $(HACL_HOME)/vale directory before invoking this Makefile" && false

.PHONY: test
test:
	$(MAKE) -C test

# 1. Generation of the .krml files
# - generate the F* dependency graph via `fstar --dep full`
# - verify every F* file in parallel to generate .checked files
# - extract each .checked file into a .krml file in parallel

FSTAR = $(FSTAR_HOME)/bin/fstar.exe --cache_checked_modules \
  $(OTHERFLAGS) \
  --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
  $(addprefix --include ,$(FSTAR_INCLUDES)) --cmi

ROOTS = EverCrypt.fst EverCrypt.Bytes.fsti EverCrypt.HKDF.fst

.PRECIOUS: %.krml %.checked

.depend: $(VALE_FSTI_HACK)
	$(FSTAR) --dep full $(ROOTS) \
	  --extract '* -Prims -FStar -C +C.Loops -EverCrypt.Bytes' > $@

include .depend

ADMIT=false

# Admit ulib + Vale-related files, verified separately with different Z3
# options. Normally the .checked files for these should already exist.
$(CACHE_DIR)/FStar.%.fst.checked: ADMIT=true
$(CACHE_DIR)/X64.%.fst.checked: ADMIT=true
$(CACHE_DIR)/Arch.%.fst.checked: ADMIT=true
$(CACHE_DIR)/Words.%.fst.checked: ADMIT=true
$(CACHE_DIR)/Vale.%.fst.checked: ADMIT=true
$(CACHE_DIR)/Collections.%.fst.checked: ADMIT=true

$(CACHE_DIR)/%.checked: | .depend
	$(FSTAR) $< \
	  --admit_smt_queries $(ADMIT) \
	  --use_hints --record_hints \
	  --hint_file $(HINT_DIR)/$(notdir $<).hints && \
	touch $@

$(OUTPUT_DIR)/%.krml: | .depend
	$(FSTAR) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

# 2. All the sources that will be part of the distribution

VALE_ASM 	= $(wildcard \
  $(HACL_HOME)/secure_api/vale/asm/aes-*.S \
  $(HACL_HOME)/secure_api/vale/asm/aes-*.asm \
  $(VALE_OBJ_DIR)/*.asm $(VALE_OBJ_DIR)/*.S)

EVERCRYPT_SOURCES = \
  $(addprefix evercrypt/c/evercrypt_,vale_stubs.c)
EVERCRYPT_MAYBE_SOURCES = \
  $(addprefix evercrypt/c/evercrypt_,openssl.c bcrypt.c bytes.c)

# 3. Distributing EverCrypt

# This achieves a pretty tight packaging of EverCrypt.
# - Modules that contain no useful declarations are -bundle'd, and since nothing
#   remains in them, no C file is generated
# - Everything else is packaged into files that start with EverCrypt_ using the
#   new rename= feature.
# - HACL* is already extracted and compiled separately, so use -library for
#   modules coming from code/
# - Use -library to ensure that modules that KreMLin generates no C file for
#   modules that are implemented by hand in C
# - Modules that export ASM symbols have -no-prefix
# - We generate a .so which statically links in libkremlib and libhacl
# - We provide hand-written C files and Vale-provided ASM files
COMPACT_FLAGS = \
  -bundle X64.*,Arch.*,Words.*,Vale.*,Collections.*,Collections,SHA_helpers \
  -bundle Prop_s,Types_s,Words_s,Views,AES_s,Workarounds,Math.*,Interop,TypesNative_s \
  -bundle 'EverCrypt.Spec.*' \
  -bundle 'Flag' \
  -bundle 'LowStar.*' \
  -bundle 'Crypto.Symmetric.*[rename=Hacl_Legacy]' \
  -bundle 'Prims,FStar.*,C,C.*[rename=EverCrypt_Kremlib]' \
  -bundle 'AEAD.*,Hacl.*,Spec.*[rename=Hacl]' -library 'Hacl.*,AEAD.*' \
  -bundle 'Check_aesni_stdcall,Check_sha_stdcall,Sha_update_bytes_stdcall[rename=Vale]' \
  -library EverCrypt.Bytes,EverCrypt.AutoConfig,EverCrypt.OpenSSL,EverCrypt.BCrypt \
  -no-prefix 'EverCrypt.Vale' \
  -no-prefix 'Sha_update_bytes_stdcall' \
  -no-prefix 'Check_sha_stdcall' \
  -no-prefix 'Check_aesni_stdcall' \
  -fparentheses -fno-shadow -fcurly-braces \
  -o libevercrypt.a

# This is for distributing to clients of libevercrypt.so, a clean header that
# exposes everything useful from EverCrypt
HEADER_FLAGS = \
  -bundle EverCrypt+EverCrypt.Bytes+EverCrypt.AutoConfig2+EverCrypt.HKDF+EverCrypt.HMAC+EverCrypt.Hash=*[rename=EverCrypt] \
  -library EverCrypt,EverCrypt.* \
  -add-include '<inttypes.h>' \
  -add-include '<stdbool.h>' \
  -add-include '<kremlin/internal/types.h>' \
  -add-include '<kremlin/internal/compat.h>' \

COPY=true

dist/header/EverCrypt.h: dist/header/Makefile.basic
dist/header/Makefile.basic: \
  EXTRA = $(HEADER_FLAGS)
dist/header/Makefile.basic: \
  COPY = false

dist/compact/Makefile.basic: \
  EXTRA = $(COMPACT_FLAGS)

# Note: EverCrypt.OpenSSL should go once we compile dist/coco with
#   EVERCRYPT_OPENSSL=false
# Note: this is not as tight as it could be because EverCrypt.fst has everything
#   while Coco just wants AES-NI
dist/coco/Makefile.basic: \
  EXTRA = $(COMPACT_FLAGS) \
  -bundle EverCrypt.Hash= -bundle EverCrypt.AutoConfig2= \
  -bundle EverCrypt= \
  -bundle EverCrypt.Hacl -bundle EverCrypt.OpenSSL \
  -bundle '\*[rename=EverCrypt_Misc]'

dist/compact-msvc/Makefile.basic: \
  EXTRA = $(COMPACT_FLAGS) -falloca -ftail-calls
dist/compact-msvc/Makefile.basic: \
  HACL_SOURCES = $(HACL_SOURCES_MSVC)

dist/%/Makefile.basic: $(ALL_KRML_FILES) | .depend
	$(KREMLIN_HOME)/krml -skip-compilation -minimal $(KOPTS) -tmpdir $(dir $@) $^ \
	  -warn-error '-6@9' \
	  -add-include '"kremlib.h"' \
	  -add-include '"kremlin/internal/compat.h"' \
	  $(notdir $(EVERCRYPT_SOURCES)) \
	  $(EXTRA)
	$(COPY) && cp $(VALE_ASM) $(EVERCRYPT_SOURCES) $(EVERCRYPT_MAYBE_SOURCES) $(dir $@) || true
	! $(COPY) && rm -rf $(dir $@)/Makefile.* || true

.PRECIOUS: dist/%/Makefile
dist/%/Makefile: dist/Makefile dist/%/Makefile.basic
	mkdir -p $(dir $@)
	cp $< $@

# 5. Compiling it

dist/%/libevercrypt.$(SO): dist/%/Makefile
	$(MAKE) -C $(dir $<)

# 6. An OCaml library that exposes only the bytes-based interface, for now

dist/compact/evercrypt.cmxa: evercrypt/ml/EverCrypt_Bytes.ml dist/compact/libevercrypt.$(SO)
	ocamlfind mklib -package ctypes,ctypes.foreign -levercrypt -Ldist/compact \
	  $(addprefix -cclib ,$(LDFLAGS)) \
	  -o $(patsubst %.cmxa,%,$@) $<

# 7. Clean targets that do not re-trigger anything except perhaps the generation
# of the .depend file.

SHELL=/bin/bash

.PHONY: clean
clean:
	rm -rf $(GENERATED_DIR) evercrypt/c/*.o libevercrypt.$(SO) libevercrypt.a
	$(MAKE) -C test clean

.PHONY: clean-c
clean-c:
	rm -rf dist
	rm -rf $(CACHE_DIR)/EverCrypt.StaticConfig.fst.checked

.PHONY: distclean
distclean: clean
	rm -rf $(OUT_DIR) $(CACHE_DIR)

