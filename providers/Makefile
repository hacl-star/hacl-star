FSTAR_HOME	?= ../../FStar
KREMLIN_HOME	?= ../../kremlin
HACL_HOME	?= ..
OPENSSL_HOME	?= ../../MLCrypto/openssl

# The everest script calls this with CONFIG=noopenssl when -windows is on
ifeq (,$(EVEREST_WINDOWS))
CONFIG		?= default
else
CONFIG		= noopenssl
endif

CACHE_DIR	= .cache
OUTPUT_DIR	= .output
HINT_DIR	= .hints
GENERATED_DIR	= generated
OUT_DIR		= out

HACL_CODE	= $(HACL_HOME)/code
HACL_SPEC	= $(HACL_HOME)/specs

# 0. The usual pseudo auto-configuration

UNAME		= $(shell uname)
SED		= $(shell which gsed >/dev/null 2>&1 && echo gsed || echo sed)
MARCH		= x86_64
ifeq ($(UNAME),Darwin)
  VARIANT	= -Darwin
  SO		= so
else ifeq ($(UNAME),Linux)
  CFLAGS	+= -fPIC
  VARIANT	= -Linux
  SO 		= so
  LDFLAGS	+= -Xlinker -z -Xlinker noexecstack -Xlinker --unresolved-symbols=report-all
else ifeq ($(OS),Windows_NT)
  CC		= $(MARCH)-w64-mingw32-gcc
  AR		= $(MARCH)-w64-mingw32-ar
  SO		= dll
endif

# Manual staging...
all:
	rm -f .depend && $(MAKE) .depend
	$(MAKE) all_

all_: $(OUT_DIR)/libevercrypt.a $(OUT_DIR)/libevercrypt.$(SO) $(OUT_DIR)/evercrypt.cmxa

.PHONY: test
test:
	$(MAKE) -C test

# 1. Generation of the .krml files
# - generate the F* dependency graph via `fstar --dep full`
# - verify every F* file in parallel to generate .checked files
# - extract each .checked file into a .krml file in parallel

FSTAR_INCLUDES = $(KREMLIN_HOME)/kremlib evercrypt evercrypt/fst \
  evercrypt/config/$(CONFIG) \
  $(HACL_CODE)/lib/kremlin \
  $(HACL_CODE)/curve25519/interfaces \
  $(HACL_CODE)/hash/interfaces \
  $(HACL_CODE)/api/interfaces \
  $(HACL_CODE)/api \
  $(HACL_CODE)/salsa-family \
  $(HACL_CODE)/poly1305 \
  $(HACL_CODE)/bignum \
  $(HACL_SPEC)

FSTAR = $(FSTAR_HOME)/bin/fstar.exe --cache_checked_modules \
  $(OTHERFLAGS) \
  --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
  $(addprefix --include ,$(FSTAR_INCLUDES))

ROOTS = EverCrypt.fst EverCrypt.Bytes.fsti

.PRECIOUS: %.krml

.depend:
	$(FSTAR) --dep full $(ROOTS) \
	  --extract '* -Prims -FStar -C +C.Loops -EverCrypt.Bytes' > $@

include .depend

# These modules fail with FStar@master.
# Please delete the target once they are fixed.
$(CACHE_DIR)/Hacl.Spec.Bignum.Fmul.fst.checked \
$(CACHE_DIR)/Hacl.Bignum.Fproduct.fst.checked \
$(CACHE_DIR)/Hacl.Spec.Poly1305_64.fst.checked \
$(CACHE_DIR)/Hacl.Impl.Chacha20.fst.checked \
$(CACHE_DIR)/Hacl.Policies.fst.checked: | .depend
	$(FSTAR) --admit_smt_queries true $< && \
	touch $@

# Admit SMT queries for modules in FStar namespace
$(CACHE_DIR)/FStar.%.fst.checked: | .depend
	$(FSTAR) --admit_smt_queries true $< && \
	touch $@

$(CACHE_DIR)/%.checked: | .depend
	$(FSTAR) $< \
	  --use_hints --record_hints --hint_info \
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

$(GENERATED_DIR)/Makefile.include: $(ALL_KRML_FILES) | .depend
	$(KREMLIN_HOME)/krml -skip-compilation -minimal \
	  $(KOPTS) \
	  -add-include '"kremlib.h"' \
	  -add-include '"kremlin/internal/compat.h"' \
	  -bundle 'FStar.*' \
	  -bundle 'C.Loops=C.Loops,Spec.*,Hacl.Spe.*,Hacl.Spec.*,Seq.*,Hacl.Endianness,Hacl.Types,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128,Hacl.Constants,Hacl.Cast' \
	  -bundle 'Hacl.Chacha20=Hacl.Impl.*,Hacl.Chacha20,Hacl.Standalone.Poly1305_64,Hacl.Lib.*,Hacl.Bignum.*' \
	  -bundle 'LowStar.*' \
	  -no-prefix 'EverCrypt.Vale' \
	  -tmpdir generated $^ -warn-error +9 \
	  && \
	touch $@

# This will generate an error the first time this Makefile is invoked because
# $(ALL_KRML_FILES) is empty. This is why we need to stage the `all` target.
-include $(GENERATED_DIR)/Makefile.include


# 3. Collecting all of our source files, and generating corresponding object
# files.

# TODO: grab these directly from Vale and error out with a helpful make target,
# like for HACL*.
VALE_DIR 	= $(HACL_HOME)/secure_api/vale/asm
VALE_SOURCES	= $(addprefix $(VALE_DIR)/,sha256_main_i.c \
  vale_aes_glue.c Vale_Hash_SHA2_256.c)
VALE_ASM 	= $(addprefix $(VALE_DIR)/,\
  sha256-$(MARCH)$(VARIANT).S aes-$(MARCH)$(VARIANT).S aesgcm-$(MARCH)$(VARIANT).S)

# TODO: understand why these two targets are broken/possibly switch to a HACL*
# branch where their compilation is restored.
# - aead-c: kremlin seems to generate an extra argument, JK had a hack to sed
#   the code in place
HACL_SOURCES	= \
  $(addprefix $(HACL_CODE)/hash/sha2-c/Hacl_SHA2_,256.c 384.c 512.c) \
  $(HACL_CODE)/curve25519/x25519-c/Hacl_Curve25519.c \
  $(HACL_CODE)/ed25519/ed25519-c/Hacl_Ed25519.c \
  $(HACL_CODE)/hmac/hmac-sha256-c/Hacl_HMAC_SHA2_256.c \
  $(HACL_CODE)/salsa-family/chacha-c/Hacl_Chacha20.c \
  $(HACL_CODE)/poly1305/poly-c/AEAD_Poly1305_64.c \
  $(HACL_CODE)/api/policies-c/Hacl_Policies.c \
  $(HACL_CODE)/api/aead-c/Hacl_Chacha20Poly1305.c

EVERCRYPT_SOURCES = \
  $(addprefix $(GENERATED_DIR)/,EverCrypt.c EverCrypt_Helpers.c EverCrypt_ValeGlue.c) \
  $(addprefix evercrypt/c/evercrypt_,autoconfig.c bytes.c vale_stubs.c)

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
ALL_OUR_FILES 	= $(filter-out Hacl_%.c AEAD_%.c FStar_%.c kremlinit.c, $(ALL_C_FILES))
ALL_GENERATED_FILES = $(addprefix $(GENERATED_DIR)/,$(ALL_OUR_FILES))

ALL_SOURCES	= $(HACL_SOURCES) $(VALE_SOURCES) $(EVERCRYPT_SOURCES) $(ALL_GENERATED_FILES)
ALL_OBJS	= $(patsubst %.c,%.o,$(ALL_SOURCES)) $(patsubst %.S,%.o,$(VALE_ASM))

INCLUDE_DIRS	= $(foreach c,$(ALL_SOURCES),$(dir $(c))) \
  $(HACL_HOME)/secure_api/out/runtime_switch/extracted \
  $(HACL_HOME)/snapshots/common $(KREMLIN_HOME)/include \
  $(OPENSSL_HOME)/include $(KREMLIN_HOME)


CFLAGS		+= $(addprefix -I ,$(INCLUDE_DIRS)) -Wall -Wextra -Werror \
  -Wno-parentheses -Wno-unused-parameter -Wno-unused-variable -Wno-infinite-recursion

#ifneq (,$(EVEREST_WINDOWS))
#FSTAR_UINT128	= ../secure_api/out/runtime_switch/uint128/FStar_UInt128.c
#ALL_GENERATED_FILES += $(FSTAR_UINT128)
#INCLUDE_DIRS	+= ../secure_api/out/runtime_switch/uint128
#CFLAGS		+= -DKRML_NOUINT128
#
#$(FSTAR_UINT128):
#	$(error Please run make -C ../secure_api before invoking this Makefile)
#endif

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

$(HACL_SOURCES):
	$(error "Please run `make -j 8 -C $(HACL_CODE) extract-c` before invoking this Makefile")

.PHONY: clean
clean:
	rm -rf $(GENERATED_DIR) evercrypt/c/*.o libevercrypt.so libevercrypt.a
	$(MAKE) -C test clean

.PHONY: distclean
distclean: clean
	rm -rf $(OUT_DIR) $(CACHE_DIR)

# 6. An OCaml library that exposes only the bytes-based interface, for now

$(OUT_DIR)/evercrypt.cmxa: evercrypt/ml/EverCrypt_Bytes.ml | $(OUT_DIR)/libevercrypt.$(SO) $(OUT_DIR)
	ocamlfind mklib -package ctypes,ctypes.foreign -levercrypt -Lout \
	  $(addprefix -cclib ,$(LDFLAGS)) \
	  -o $(patsubst %.cmxa,%,$@) $^
