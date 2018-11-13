include Makefile.common

# 0. The usual pseudo auto-configuration

UNAME		= $(shell uname)
SED		= $(shell which gsed >/dev/null 2>&1 && echo gsed || echo sed)
MARCH		= x86_64
ifeq ($(UNAME),Darwin)
  VARIANT	= -darwin
  SO		= so
else ifeq ($(UNAME),Linux)
  CFLAGS	+= -fPIC
  VARIANT	= -linux
  SO 		= so
  LDFLAGS	+= -Xlinker -z -Xlinker noexecstack -Xlinker --unresolved-symbols=report-all
else ifeq ($(OS),Windows_NT)
  CC		= $(MARCH)-w64-mingw32-gcc
  AR		= $(MARCH)-w64-mingw32-ar
  VARIANT	= -mingw
  SO		= dll
endif

VALE_FSTI_HACK	= $(HACL_HOME)/vale/code/arch/x64/interop/fsti
HACL_CHECK	= $(HACL_HOME)/code/dist/compact/Makefile.include

# Manual staging
all: $(VALE_FSTI_HACK) $(VALE_OBJ_DIR) $(HACL_CHECK)
	rm -f .depend && $(MAKE) .depend
	$(MAKE) stage1
	STAGE=2 $(MAKE) stage2
	$(MAKE) -C quic_provider

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

$(HACL_CHECK):
	@echo "Please run make in the $(HACL_HOME)/code directory before invoking this Makefile" && false

stage1: $(GENERATED_DIR)/Makefile.include $(INCLUDE_DIR)/EverCrypt.h

stage2: $(OUT_DIR)/libevercrypt.a $(OUT_DIR)/libevercrypt.$(SO) $(OUT_DIR)/evercrypt.cmxa

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
# options.
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

# 2. Generation of the .c files
ifneq (,$(EVEREST_WINDOWS))
KOPTS		+=-falloca -ftail-calls
endif

VALE_BUNDLES=$(addprefix -bundle , 'X64.*' 'Arch.*' 'Words.*' 'Vale.*' \
  'Collections.*' 'SHA_helpers' Prop_s Collections Types_s Words_s Views AES_s \
  Workarounds 'Math.*' Interop TypesNative_s)

$(GENERATED_DIR)/Makefile.include: $(ALL_KRML_FILES) | .depend
	$(KREMLIN_HOME)/krml -skip-compilation -minimal \
	  $(KOPTS) \
	  -warn-error '-6' \
	  -add-include '"kremlib.h"' \
	  -add-include '"kremlin/internal/compat.h"' \
	  $(VALE_BUNDLES) \
	  -bundle 'Prims,FStar.*,C,C.*[rename=EverCrypt_Kremlib]' \
	  -bundle 'EverCrypt.Spec.*' \
	  -bundle 'Crypto.Symmetric.*[rename=Hacl_Legacy]' \
	  -bundle 'Flag' \
	  -bundle 'Spec.*' \
	  -bundle 'LowStar.*' \
	  -bundle 'AEAD.*,Hacl.*[rename=Hacl]' -library 'Hacl.*,AEAD.*' \
	  -bundle 'Check_aesni_stdcall,Check_sha_stdcall,Sha_update_bytes_stdcall[rename=Vale]' \
	  -no-prefix 'EverCrypt.Vale' \
	  -no-prefix 'Sha_update_bytes_stdcall' \
	  -no-prefix 'Check_sha_stdcall' \
	  -no-prefix 'Check_aesni_stdcall' \
	  -tmpdir $(GENERATED_DIR) $^ -warn-error @9

$(INCLUDE_DIR)/EverCrypt.h: $(ALL_KRML_FILES) | .depend
	$(KREMLIN_HOME)/krml -skip-compilation -minimal \
	  $(KOPTS) \
	  -bundle EverCrypt+EverCrypt.Bytes+EverCrypt.AutoConfig+EverCrypt.HKDF+EverCrypt.HMAC+EverCrypt.Hash=*[rename=EverCrypt]\
	  -library EverCrypt,EverCrypt.* \
	  -add-include '<inttypes.h>' \
	  -add-include '<stdbool.h>' \
	  -add-include '<kremlin/internal/types.h>' \
	  -add-include '<kremlin/internal/compat.h>' \
	  -tmpdir $(INCLUDE_DIR) $^
	rm -rf $(INCLUDE_DIR)/Makefile.include $(INCLUDE_DIR)/*.c



# The Makefile is manually staged because GNU Make does not understand
# dependencies between the Makefiles we include, i.e. it won't first generate
# the .depend, parse it, then generate Makefile.include, parse it, then
# generate dependencies among the C files
ifeq ($(STAGE),2)

# The top-level invocation guarantees that stage1 has been run and this file is
# there.
include $(GENERATED_DIR)/Makefile.include

# 3. Collecting all of our source files, and generating corresponding object
# files.

VALE_ASM 	= $(HACL_HOME)/secure_api/vale/asm/aes-$(MARCH)$(VARIANT).S \
  $(patsubst %,$(VALE_OBJ_DIR)/%-$(MARCH)$(VARIANT).S,sha256 aesgcm curve25519 cpuid)

HACL_SOURCES	= $(wildcard $(HACL_CODE)/dist/compact/*.c)

EVERCRYPT_SOURCES = \
  $(addprefix evercrypt/c/evercrypt_,bytes.c autoconfig.c vale_stubs.c)

ifeq ($(CONFIG),noopenssl)
EVERCRYPT_SOURCES += evercrypt/c/evercrypt_bcrypt.c
else
EVERCRYPT_SOURCES += evercrypt/c/evercrypt_openssl.c
endif

# This is auto-generated by KreMLin; since the Makefile is staged via the
# inclusion of Makefile.include, the automated dependency analysis via $(CC) -MM
# also captures the dependencies between these files.
#
# KreMLin sees the fsti's for the various Hacl_* modules and creates .h/.c
# files for them in generated/. However, we are only interested in the header,
# and drop these (mostly empty) C files, since the "real" ones are collected via
# HACL_SOURCES above.
ALL_GENERATED_FILES = $(addprefix $(GENERATED_DIR)/,$(ALL_C_FILES))

ALL_SOURCES	= $(HACL_SOURCES) $(VALE_SOURCES) $(EVERCRYPT_SOURCES) $(ALL_GENERATED_FILES)
ALL_OBJS	= $(patsubst %.c,%.o,$(ALL_SOURCES)) $(patsubst %.S,%.o,$(VALE_ASM))

INCLUDE_DIRS	= $(foreach c,$(ALL_SOURCES),$(dir $(c))) \
  $(HACL_HOME)/secure_api/out/runtime_switch/extracted \
  $(HACL_HOME)/snapshots/common $(KREMLIN_HOME)/include \
  $(OPENSSL_HOME)/include $(KREMLIN_HOME)


CFLAGS		+= $(addprefix -I ,$(INCLUDE_DIRS)) -Wall -Wextra -Werror -Wno-unknown-warning-option \
  -Wno-parentheses -Wno-unused-parameter -Wno-unused-variable -Wno-unused-but-set-variable -Wno-infinite-recursion -g

# GNU Make manual section 4.14
%.d: %.c
	@set -e; rm -f $@; \
	  $(CC) -MM $(CFLAGS) $< > $@.$$$$; \
	  sed 's,\($(notdir $*)\)\.o[ :]*,$(dir $@)\1.o $@ : ,g' < $@.$$$$ > $@; \
	  rm -f $@.$$$$

-include $(patsubst %.c,%.d,$(ALL_SOURCES))

$(OUT_DIR):
	mkdir -p $@

# 4. Collecting all of the object files into a static and a dynamic library.

ifeq (,$(EVEREST_WINDOWS))
LDFLAGS += -L$(OPENSSL_HOME) -lcrypto
else
LDFLAGS += -lbcrypt
endif

ifeq ($(UNAME),Linux)
LDFLAGS += -ldl -lpthread
endif

LIBKREMLIB = $(KREMLIN_HOME)/kremlib/out/libkremlib.a

$(LIBKREMLIB):
	$(error Please run make -C $(KREMLIN_HOME)/kremlib to generate libkremlib.a)

# Note: see
# https://www.gnu.org/software/make/manual/html_node/Archive-Pitfalls.html#Archive-Pitfalls
# for why we are not using libhacl.a($(OBJS))
$(OUT_DIR)/libevercrypt.a: $(ALL_OBJS) | $(OUT_DIR)
	$(AR) cr $@ $^

$(OUT_DIR)/libevercrypt.$(SO): $(ALL_OBJS) | $(OUT_DIR)
	$(CC) -shared $^ $(LDFLAGS) -o $@ $(LIBKREMLIB)

.PRECIOUS: %.o

# 6. An OCaml library that exposes only the bytes-based interface, for now

$(OUT_DIR)/evercrypt.cmxa: evercrypt/ml/EverCrypt_Bytes.ml | $(OUT_DIR)/libevercrypt.$(SO) $(OUT_DIR)
	ocamlfind mklib -package ctypes,ctypes.foreign -levercrypt -Lout \
	  $(addprefix -cclib ,$(LDFLAGS)) \
	  -o $(patsubst %.cmxa,%,$@) $^

endif # COMPILE

# 7. Clean targets that do not re-trigger anything except perhaps the generation
# of the .depend file.

SHELL=/bin/bash

.PHONY: clean
clean:
	rm -rf $(GENERATED_DIR) evercrypt/c/*.o libevercrypt.$(SO) libevercrypt.a
	$(MAKE) -C test clean

.PHONY: clean-c
clean-c:
	rm -rf $(GENERATED_DIR)/{*.{c,h},Makefile.include}
	rm -rf $(CACHE_DIR)/EverCrypt.StaticConfig.fst.checked

.PHONY: distclean
distclean: clean
	rm -rf $(OUT_DIR) $(CACHE_DIR)

