all: compile verify extract test

include Makefile.common

# Old targets, backwards-compat:
.PHONY: old-%
old-%:
	$(MAKE) -C old -f Makefile.old $*

# 0. Paths and includes

ROOTS = $(wildcard $(addsuffix /*.fst,$(DIRS)))

ALL_CHECKED_FILES = $(addsuffix .checked,$(ROOTS))


# 1. Top-level entry points for this Makefile

verify: $(ALL_CHECKED_FILES)

extract: dist/compact/Makefile.basic dist/generic/Makefile.basic \
  dist/compact-msvc/Makefile.basic

compile: compile-compact compile-generic compile-compact-msvc

# Backwards compat
extract: old-extract-c

test: test-Test_SHA3 test-Test_CSHAKE

clean: clean-c
	find $(DIRS) -iname '*.checked' | xargs rm -rf

clean-c: old-clean-c
	rm -rf $(OUTPUT_DIR)

# 2. Verification

%.checked:
	$(FSTAR) $< && \
	touch $@

# 3. Extraction. Note that all the C files are prefixed with Hacl_. Cleaner!

.PRECIOUS: %.krml

$(OUTPUT_DIR)/%.krml:
	$(FSTAR) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

COMPACT_FLAGS=-bundle Hacl.Hash.MD5+Hacl.Hash.Core.MD5+Hacl.Hash.SHA1+Hacl.Hash.Core.SHA1+Hacl.Hash.SHA2+Hacl.Hash.Core.SHA2+Hacl.Hash.Core.SHA2.Constants=Hacl.Hash.*[rename=Hacl_Hash] \
  -bundle Hacl.Impl.SHA3,Hacl.SHA3=[rename=Hacl_SHA3] \
  -bundle Prims \
  -bundle LowStar.* \
  -bundle C,C.Loops,Spec.Loops,C.Endianness,FStar.*[rename=Hacl_Kremlib] \
  -bundle Test.* \
  -minimal \
  -add-include '"kremlin/internal/types.h"' \
  -add-include '"kremlin/c_endianness.h"' \
  -add-include '<string.h>' \
  -fno-shadow -fcurly-braces

DEFAULT_FLAGS=\
  -library Lib.PrintBuffer,Lib.RandomBuffer

# For the time being, we rely on the old extraction to give us self-contained
# files
HACL_OLD_FILES=\
  old/curve25519/x25519-c/Hacl_Curve25519.c \
  old/ed25519/ed25519-c/Hacl_Ed25519.c \
  old/salsa-family/chacha-c/Hacl_Chacha20.c \
  old/poly1305/poly-c/AEAD_Poly1305_64.c \
  old/poly1305/poly-c/Hacl_Poly1305_64.c \
  old/api/aead-c/Hacl_Chacha20Poly1305.c

dist/compact/Makefile.basic: EXTRA=$(COMPACT_FLAGS)

dist/compact-msvc/Makefile.basic: EXTRA=$(COMPACT_FLAGS) -falloca -ftail-calls

dist/%/Makefile.basic: $(ALL_KRML_FILES) | old-extract-c
	mkdir -p $(dir $@)
	cp $(HACL_OLD_FILES) $(patsubst %.c,%.h,$(HACL_OLD_FILES)) $(dir $@)
	cp $(wildcard $(LIB_DIR)/c/*.c) $(dir $@)
	$(KRML) $(DEFAULT_FLAGS) $(EXTRA) \
	  -tmpdir $(dir $@) -skip-compilation \
	  -bundle Spec.*[rename=Hacl_Spec] $^ \
	  -ccopt -Wno-unused \
	  -warn-error @4 \
	  -fparentheses \
	  $(notdir $(HACL_OLD_FILES)) \
	  $(notdir $(wildcard $(LIB_DIR)/c/*.c)) \
	  -o libhacl.a

dist/test/%.c: $(ALL_KRML_FILES)
	$(KRML) $(DEFAULT_FLAGS) \
	  -tmpdir $(dir $@) -skip-compilation \
	  -no-prefix $(subst Test_,Test.,$*) \
	  -library Hacl \
	  -fparentheses -fcurly-braces -fno-shadow \
	  -bundle '$(subst Test_,Test.)=*'

# 4. Compilation

compile-%: dist/%/Makefile.basic
	$(MAKE) -C $(dir $<) -f $(notdir $<)

dist/test/%.exe: dist/test/%.c compile-generic
	# Linking with full kremlib since tests may use TestLib, etc.
	$(CC) -Wall -Wextra -Werror $< -o $@ dist/generic/libhacl.a \
	  $(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a

test-%: dist/test/%.exe
	$@
