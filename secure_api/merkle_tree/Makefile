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
  $(HACL_HOME)/specs \
  $(HACL_HOME)/code/lib \
  $(HACL_HOME)/code/hash-new \
  $(HACL_HOME)/providers/evercrypt \
  $(KREMLIN_HOME)/kremlib \
  $(HACL_HOME)/vale/code/arch/x64/interop/fsti \
  $(HACL_HOME)/vale/code/arch/x64 \
  $(HACL_HOME)/vale/specs/defs \
  $(HACL_HOME)/vale/specs/hardware \
  $(HACL_HOME)/vale/code/crypto/sha \
  $(HACL_HOME)/vale/code/arch \
  $(HACL_HOME)/vale/code/lib/collections \
  $(HACL_HOME)/vale/code/lib/util \
  $(HACL_HOME)/vale/specs/crypto \
  $(HACL_HOME)/vale/specs/math \
  $(HACL_HOME)/vale/obj/cache_checked


FSTAR_INCLUDES = $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(OTHERFLAGS) \
  --cache_checked_modules --cache_dir $(CACHE_DIR) \
  --odir $(OUTPUT_DIR) $(FSTAR_INCLUDES) --cmi \
  --use_hints --use_hint_hashes --record_hints --query_stats

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

ADMIT=false

# JP: to be fixed with --already_cached
$(CACHE_DIR)/FStar.%.checked: ADMIT=true
$(CACHE_DIR)/LowStar.%.checked: ADMIT=true
$(CACHE_DIR)/C.%.checked: ADMIT=true
$(CACHE_DIR)/prims.fst.checked: ADMIT=true
$(CACHE_DIR)/Spec.Loops.fst.checked: ADMIT=true
$(CACHE_DIR)/Spec.Matrix.fst.checked: ADMIT=true

$(CACHE_DIR)/%.checked: | .depend $(HINT_DIR)
	$(FSTAR) $< --admit_smt_queries $(ADMIT) \
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
  $(HACL_HOME)/code/dist/compact/libhacl.a \
  $(KREMLIN_HOME)/kremlib/dist/minimal/libkremlib.a
	$(CC) $(CFLAGS) -Idist/compact -I$(KREMLIN_HOME)/include \
	  -I$(HACL_HOME)/providers/dist/compact $^ -o $@


# This snapshot assumes EverCrypt is built via `CONFIG=everest make` $(HACL_HOME)/providers
.PHONY: snapshot2
snapshot2: $(ALL_SOURCES)
	mkdir -p snapshot
	mkdir -p snapshot/kremlin
	mkdir -p snapshot/kremlin/kremlib/extracted
	cp -R $(KREMLIN_HOME)/include snapshot/kremlin/include
	cp -R $(KREMLIB)/extracted/*.{c,h} snapshot/kremlin/kremlib/extracted
	cp -R $(KREMLIB)/c/*.c snapshot/kremlin
	mkdir -p snapshot/hacl
	cp -R $(HACL_HOME)/code/dist/compact/*.{c,h} snapshot/hacl
	mkdir -p snapshot/evercrypt/include
	mkdir -p snapshot/evercrypt/generated
	mkdir -p snapshot/evercrypt/c
	cp -R $(HACL_HOME)/providers/include/*.h snapshot/evercrypt/include
	cp $(HACL_HOME)/providers/generated/*.{c,h} snapshot/evercrypt/generated
	rm -f snapshot/evercrypt/generated/AEAD_Poly1305_64.{c,h}
	for i in evercrypt_autoconfig.c; do cp $(HACL_HOME)/providers/evercrypt/c/$$i snapshot/evercrypt/c; done
	mkdir -p snapshot/vale
	for i in $(VALE_ASM); do cp $$i snapshot/vale; done
	cp -R $(GENERATED_DIR)/*.h snapshot
	for i in $(ALL_SOURCES); do cp $$i snapshot; done
	for i in $(ALL_TEST_FILES); do cp $$i snapshot; done
	cp MerkleTree.h snapshot
	rm -f snapshot/kremlin/kremlib/extracted/FStar_UInt.c
