all: verify extract test

# Old targets, backwards-compat:
.PHONY: old-%
old-%:
	$(MAKE) -f Makefile.old $*

# 0. Paths and includes

HACL_HOME ?= ..

HASH_DIR=$(HACL_HOME)/code/hash-new

ROOTS=$(addprefix $(HASH_DIR)/Hacl.Hash.,MD5.fst SHA1.fst SHA2.fst)

ALL_CHECKED_FILES = $(addsuffix .checked,$(ROOTS))

.depend:
	@$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar +FStar.Endianness +FStar.Kremlin.Endianness' > $@

include .depend

include Makefile.common

# 1. Top-level entry points for this Makefile

verify: $(ALL_CHECKED_FILES)

extract: dist/compact/Makefile.include dist/generic/Makefile.include

# Backwards compat target name
extract-c: extract old-extract-c

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

dist/compact/Makefile.include: \
  EXTRA=-bundle Hacl.Hash.MD5+Hacl.Hash.Core.MD5+Hacl.Hash.SHA1+Hacl.Hash.Core.SHA1+Hacl.Hash.SHA2+Hacl.Hash.Core.SHA2+Hacl.Hash.Core.SHA2.Constants=Hacl.Hash.*[rename=Hacl_Hash] \
    -bundle Prims \
    -bundle LowStar.* \
    -bundle C,C.Loops,Spec.Loops,C.Endianness,FStar.*[rename=Hacl_Kremlib] \
    -minimal \
    -add-include '"kremlin/internal/types.h"' \
    -add-include '"kremlin/c_endianness.h"' \
    -add-include '<string.h>' \
    -fparentheses -fno-shadow -fcurly-braces

# For the time being, we rely on the old extraction to give us self-contained
# files
HACL_OLD_FILES=\
  curve25519/x25519-c/Hacl_Curve25519.c \
  ed25519/ed25519-c/Hacl_Ed25519.c \
  salsa-family/chacha-c/Hacl_Chacha20.c \
  poly1305/poly-c/AEAD_Poly1305_64.c \
  poly1305/poly-c/Hacl_Poly1305_64.c \
  api/aead-c/Hacl_Chacha20Poly1305.c

dist/%/Makefile.include: $(ALL_KRML_FILES) old-extract-c
	mkdir -p $(dir $@)
	cp $(HACL_OLD_FILES) $(patsubst %.c,%.h,$(HACL_OLD_FILES)) $(dir $@)
	$(KRML) $(EXTRA) -tmpdir $(dir $@) -skip-compilation \
	  -bundle Spec.*[rename=Hacl_Spec] $^ \
	  -warn-error @4
