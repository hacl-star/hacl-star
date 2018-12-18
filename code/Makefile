all: compile verify extract test

# Old targets, backwards-compat:
.PHONY: old-%
old-%:
	$(MAKE) -C old -f Makefile.old $*

# 0. Paths and includes

HACL_HOME ?= ..

HASH_DIR=$(HACL_HOME)/code/hash

ROOTS=$(addprefix $(HASH_DIR)/Hacl.Hash.,MD5.fst SHA1.fst SHA2.fst)

ALL_CHECKED_FILES = $(addsuffix .checked,$(ROOTS))

.PHONY: .depend
.depend:
	@$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar +FStar.Endianness +FStar.Kremlin.Endianness' > $@

include .depend

include Makefile.common

# 1. Top-level entry points for this Makefile

verify: $(ALL_CHECKED_FILES)

extract: dist/compact/Makefile.basic dist/generic/Makefile.basic \
  dist/compact-msvc/Makefile.basic

compile: compile-compact compile-generic compile-compact-msvc

# Backwards compat
extract: old-extract-c

clean: clean-c
	find $(DIRS) -iname '*.checked' | xargs rm -rf

clean-c: old-clean-c
	rm -rf $(OUTPUT_DIR)

test:

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
    -bundle Prims \
    -bundle LowStar.* \
    -bundle C,C.Loops,Spec.Loops,C.Endianness,FStar.*[rename=Hacl_Kremlib] \
    -minimal \
    -add-include '"kremlin/internal/types.h"' \
    -add-include '"kremlin/c_endianness.h"' \
    -add-include '<string.h>' \
    -fno-shadow -fcurly-braces

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
	$(KRML) $(EXTRA) -tmpdir $(dir $@) -skip-compilation \
	  -bundle Spec.*[rename=Hacl_Spec] $^ \
	  -ccopts -Wno-unused-variable,-Wno-unused-but-set-variable \
	  -ccopts -Wno-parentheses,-Wno-unused-parameter \
	  -warn-error @4 \
	  -fparentheses \
	  $(notdir $(HACL_OLD_FILES)) \
	  -o libhacl.a

# 4. Compilation

compile-%: dist/%/Makefile.basic
	$(MAKE) -C $(dir $<) -f $(notdir $<)
