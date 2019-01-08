# This Makefile is borrowed heavily from:
# https://github.com/project-everest/hacl-star/blob/frodo_sn/frodo/code/Makefile

FSTAR_HOME ?= ../../../FStar
KREMLIN_HOME ?= ../../../kremlin
HACL_HOME ?= ../..

CACHE_DIR = .cache
OUTPUT_DIR = .output
HINT_DIR = .hints

KREMLIN=$(KREMLIN_HOME)/krml

ALL_TEST_FILES= \
  ./test/merkle_tree_test.h \
  ./test/merkle_tree_test.c

all:
	rm -f .depend && $(MAKE) .depend
	$(MAKE) all_

all_: dist/compact/libmerkletree.a

# 1. Generation of .krml files
# - generate the F* dependency graph via `fstar --dep full`
# - verify every F* file in parallel to generate .checked files
# - extract each .checked file into a .krml file in parallel

FSTAR_INCLUDE_DIRS = \
  $(KREMLIN_HOME)/kremlib/compat \
  $(KREMLIN_HOME)/kremlib \
  $(HACL_HOME)/specs \
  $(HACL_HOME)/providers/evercrypt \
  $(HACL_HOME)/providers/evercrypt/fst \
  $(HACL_HOME)/providers/evercrypt/config/$(CONFIG) \
  $(HACL_HOME)/code/hash \
  $(HACL_HOME)/code/old/lib/kremlin \
  $(HACL_HOME)/code/old/experimental/aesgcm \
  $(HACL_HOME)/code/old/curve25519/interfaces \
  $(HACL_HOME)/code/old/api/interfaces \
  $(HACL_HOME)/code/old/api \
  $(HACL_HOME)/code/old/salsa-family \
  $(HACL_HOME)/code/old/poly1305 \
  $(HACL_HOME)/code/old/bignum \
  $(HACL_HOME)/vale/code/lib/math \
  $(HACL_HOME)/vale/code/lib/util \
  $(HACL_HOME)/vale/code/lib/collections \
  $(HACL_HOME)/vale/code/arch/x64/interop \
  $(HACL_HOME)/vale/code/arch/x64 \
  $(HACL_HOME)/vale/code/arch \
  $(HACL_HOME)/vale/code/crypto/poly1305/x64 \
  $(HACL_HOME)/vale/code/crypto/aes \
  $(HACL_HOME)/vale/code/crypto/sha \
  $(HACL_HOME)/vale/code/crypto/ecc/curve25519 \
  $(HACL_HOME)/vale/specs/math \
  $(HACL_HOME)/vale/specs/defs \
  $(HACL_HOME)/vale/specs/crypto \
  $(HACL_HOME)/vale/specs/hardware \

EVERCRYPT_CACHE_DIR=$(HACL_HOME)/providers/.cache

# Still be cool with a not-built EverCrypt in interactive mode
ifneq (,$(wildcard $(EVERCRYPT_CACHE_DIR)))
  FSTAR_INCLUDE_DIRS += $(EVERCRYPT_CACHE_DIR)
endif

VALE_OBJ_DIR=$(HACL_HOME)/vale/obj

VALE_OBJ_INCLUDE_DIRS = \
  $(VALE_OBJ_DIR)/cache_checked \
  $(VALE_OBJ_DIR)/code/lib/util/x64/stdcalls \
  $(VALE_OBJ_DIR)/code/lib/util/x64 \
  $(VALE_OBJ_DIR)/code/lib/util \
  $(VALE_OBJ_DIR)/code/arch/x64 \
  $(VALE_OBJ_DIR)/code/crypto/aes/x64/stdcalls \
  $(VALE_OBJ_DIR)/code/crypto/aes/x64 \
  $(VALE_OBJ_DIR)/code/thirdPartyPorts/Intel/aes/x64 \
  $(VALE_OBJ_DIR)/code/thirdPartyPorts/OpenSSL/poly1305/x64 \
  $(VALE_OBJ_DIR)/code/thirdPartyPorts/OpenSSL/sha \
  $(VALE_OBJ_DIR)/code/thirdPartyPorts/rfc7748/curve25519/x64 \
  $(VALE_OBJ_DIR)/code/test \

ifneq (,$(wildcard $(VALE_OBJ_DIR)))
  FSTAR_INCLUDE_DIRS += $(VALE_OBJ_INCLUDE_DIRS)
endif

FSTAR_INCLUDES = $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(OTHERFLAGS) \
  --cache_checked_modules --cache_dir $(CACHE_DIR) \
  --odir $(OUTPUT_DIR) $(FSTAR_INCLUDES) --cmi \
  --use_hints --use_hint_hashes --record_hints --query_stats \
  --already_cached '* -MerkleTree'

$(HINT_DIR):
	mkdir -p $@

%.fst-in %.fsti-in: $(HINT_DIR)
	@echo --cache_checked_modules --cache_dir $(CACHE_DIR) \
	$(FSTAR_INCLUDES) \
	$(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fst.hints

ROOTS = MerkleTree.New.Low.fst MerkleTree.New.Low.Serialization.fst

# We don't want to delete .krml files during extraction.
.PRECIOUS: %.krml

.depend:
	$(FSTAR) --dep full $(ROOTS) --extract '* -FStar -Spec' > $@

include .depend

$(CACHE_DIR)/%.checked: | .depend $(HINT_DIR)
	$(FSTAR) $< \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $<).hints && \
	touch $@

$(OUTPUT_DIR)/%.krml: | .depend
	$(FSTAR) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

# 2. Generation of .c files
#
CFLAGS += -O3 -march=native -mtune=native -funroll-loops

.PRECIOUS: dist/%/Makefile.basic
dist/%/Makefile.basic: $(ALL_KRML_FILES) | .depend
	$(KREMLIN) -skip-compilation \
	  -no-prefix 'MerkleTree.New.Low' \
	  -no-prefix 'MerkleTree.New.Low.Serialization' \
	  -add-include '"kremlin/internal/compat.h"' \
	  -bundle Prims,FStar.*,LowStar.*,C,C.*[rename=Merkle_Kremlib] \
	  -bundle MerkleTree.New.Low= \
	  -bundle MerkleTree.New.Low.Serialization= \
	  -bundle '*[rename=Merkle_EverCrypt]' \
	  -library 'EverCrypt,EverCrypt.*' \
	  -tmpdir $(dir $@) \
	  $(addprefix -ccopt ,$(CFLAGS)) \
	  -warn-error +9 \
	  -fparentheses -fcurly-braces -fno-shadow \
	  -o libmerkletree.a \
	  $^

dist/%/libmerkletree.a: dist/%/Makefile.basic
	$(MAKE) -C $(dir $@) -f Makefile.basic

# Tests. Use CFLAGS="-fsanitize=address -fno-omit-frame-pointer" to run Clang
# sanitizers.

test: test/merkle_tree_test.exe
	./$<

test/merkle_tree_test.exe: test/merkle_tree_test.c dist/compact/libmerkletree.a \
  $(HACL_HOME)/providers/dist/coco/libevercrypt.a \
  $(HACL_HOME)/dist/compact/libhacl.a \
  $(KREMLIN_HOME)/kremlib/dist/minimal/libkremlib.a
	$(CC) $(CFLAGS) -Idist/compact -I$(KREMLIN_HOME)/include \
	  -I$(HACL_HOME)/providers/dist/compact $^ -o $@


# This snapshot assumes EverCrypt is built via `CONFIG=everest make` $(HACL_HOME)/providers
.PHONY: make-snapshot
make-snapshot:
	mkdir -p snapshot/kremlib
	cp -R $(KREMLIN_HOME)/kremlib/dist/minimal/ snapshot/kremlib/
	mkdir -p snapshot/include
	cp -R $(KREMLIN_HOME)/include/ snapshot/include/
	mkdir -p snapshot/hacl
	cp -R $(HACL_HOME)/code/dist/compact/ snapshot/hacl/
	mkdir -p snapshot/evercrypt
	cp -R $(HACL_HOME)/providers/dist/coco/ snapshot/evercrypt/
	mkdir -p snapshot/merkle
	cp -R dist/compact snapshot/merkle/
