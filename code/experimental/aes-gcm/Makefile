FSTAR_HOME   ?= ../../../../FStar
KREMLIN_HOME ?= ../../../../kremlin
HACL_HOME    ?= ../../..

CACHE_DIR     = .cache
OUTPUT_DIR    = .output
HINT_DIR      = .hints
GENERATED_DIR = x25519-c
OUT_DIR	      = x25519-c

.PHONY: all test stage1 stage2 clean clean-c distclean

all: aesgcm-ni.exe aesgcm-m32.exe

verify: test

#CC=/usr/local/Cellar/llvm/7.0.0/bin/clang-7
CC=gcc


AESGCM_NI_FILES= $(HACL_HOME)/lib/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/Lib.RawIntTypes.fst \
	$(HACL_HOME)/lib/Lib.Buffer.fst \
	$(HACL_HOME)/lib/Lib.ByteBuffer.fst \
	$(HACL_HOME)/lib/Lib.Loops.fst \
	$(HACL_HOME)/lib/Lib.IntVector.fst \
	$(HACL_HOME)/lib/Lib.IntVector.Intrinsics.fsti \
	$(HACL_HOME)/lib/Lib.Sequence.Lemmas.fst \
	$(HACL_HOME)/lib/Lib.Sequence.Lemmas.fsti \
	../gf128/Hacl.Impl.Gf128.FieldNI.fst \
	../gf128/Hacl.Impl.Gf128.Fields.fst \
	../gf128/Hacl.Spec.GF128.Equiv.fst \
	../gf128/Hacl.Impl.Gf128.Generic.fst \
	../gf128/Hacl.Gf128.NI.fst \
	../aes/Hacl.Impl.AES.CoreNI.fst \
	../aes/Hacl.Impl.AES.Core.fst \
	../aes/Hacl.Impl.AES.Generic.fst \
	../aes/Hacl.AES_128.NI.fst \
	Hacl.AES_128_GCM.NI.fst

AESGCM_AES256_NI_FILES= $(HACL_HOME)/lib/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/Lib.RawIntTypes.fst \
	$(HACL_HOME)/lib/Lib.Buffer.fst \
	$(HACL_HOME)/lib/Lib.ByteBuffer.fst \
	$(HACL_HOME)/lib/Lib.Loops.fst \
	$(HACL_HOME)/lib/Lib.IntVector.fst \
	$(HACL_HOME)/lib/Lib.IntVector.Intrinsics.fsti \
	$(HACL_HOME)/lib/Lib.Sequence.Lemmas.fst \
	$(HACL_HOME)/lib/Lib.Sequence.Lemmas.fsti \
	../gf128/Hacl.Impl.Gf128.FieldNI.fst \
	../gf128/Hacl.Impl.Gf128.Fields.fst \
	../gf128/Hacl.Spec.GF128.Equiv.fst \
	../gf128/Hacl.Impl.Gf128.Generic.fst \
	../gf128/Hacl.Gf128.NI.fst \
	../aes/Hacl.Impl.AES.CoreNI.fst \
	../aes/Hacl.Impl.AES.Core.fst \
	../aes/Hacl.Impl.AES.Generic.fst \
	../aes/Hacl.AES_256.NI.fst \
	Hacl.AES_256_GCM.NI.fst

AESGCM_M32_FILES= $(HACL_HOME)/lib/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/Lib.RawIntTypes.fst \
	$(HACL_HOME)/lib/Lib.Buffer.fst \
	$(HACL_HOME)/lib/Lib.ByteBuffer.fst \
	$(HACL_HOME)/lib/Lib.Loops.fst \
	$(HACL_HOME)/lib/Lib.Sequence.Lemmas.fst \
	$(HACL_HOME)/lib/Lib.Sequence.Lemmas.fsti \
	../gf128/Hacl.Impl.Gf128.FieldPreComp.fst \
	../gf128/Hacl.Impl.Gf128.Fields.fst \
	../gf128/Hacl.Spec.GF128.Equiv.fst \
	../gf128/Hacl.Impl.Gf128.Generic.fst \
	../gf128/Hacl.Gf128.PreComp.fst \
	../aes/Hacl.Impl.AES.CoreBitSlice.fst \
	../aes/Hacl.Impl.AES.Core.fst \
	../aes/Hacl.Impl.AES.Generic.fst \
	../aes/Hacl.AES_128.BitSlice.fst \
	Hacl.AES_128_GCM.M32.fst

AESGCM_AES256_M32_FILES= $(HACL_HOME)/lib/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/Lib.RawIntTypes.fst \
	$(HACL_HOME)/lib/Lib.Buffer.fst \
	$(HACL_HOME)/lib/Lib.ByteBuffer.fst \
	$(HACL_HOME)/lib/Lib.Loops.fst \
	$(HACL_HOME)/lib/Lib.Sequence.Lemmas.fst \
	$(HACL_HOME)/lib/Lib.Sequence.Lemmas.fsti \
	../gf128/Hacl.Impl.Gf128.FieldPreComp.fst \
	../gf128/Hacl.Impl.Gf128.Fields.fst \
	../gf128/Hacl.Spec.GF128.Equiv.fst \
	../gf128/Hacl.Impl.Gf128.Generic.fst \
	../gf128/Hacl.Gf128.PreComp.fst \
	../aes/Hacl.Impl.AES.CoreBitSlice.fst \
	../aes/Hacl.Impl.AES.Core.fst \
	../aes/Hacl.Impl.AES.Generic.fst \
	../aes/Hacl.AES_256.BitSlice.fst \
	Hacl.AES_256_GCM.M32.fst



KREMLIN_ARGS:=-funroll-loops 8 -warn-error +9 -I $(HACL_HOME)/lib -I $(KREMLIN_HOME)/kremlib -I $(HACL_HOME)/specs -I . -I $(HACL_HOME)/code/experimental/aes -I $(HACL_HOME)/code/experimental/gf128 -ccopt '-march=native' -fbuiltin-uint128 -drop FStar.UInt128 -fnocompound-literals -fparentheses -fcurly-braces

aesgcm-ni-c/out.krml: $(AESGCM_NI_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir aesgcm-ni-c $(AESGCM_NI_FILES) -skip-translation

aesgcm-ni-c/Hacl_AES_128_GCM_NI.c: aesgcm-ni-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir aesgcm-ni-c  $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -add-include '"libintvector.h"' -drop Lib.IntVector.Intrinsics -bundle 'Hacl.AES_128_GCM.NI=*'

aesgcm-ni.exe: aesgcm-ni-c/Hacl_AES_128_GCM_NI.c aesgcm-ni-test.c
	$(CC) -march=native -mtune=native -O3 -I $(HACL_HOME)/lib/c -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . aesgcm-ni-c/Hacl_AES_128_GCM_NI.c $(KREMLIN_HOME)/kremlib/dist/generic/testlib.o aesgcm-ni-test.c -o aesgcm-ni.exe
	./aesgcm-ni.exe



aesgcm-aes256-ni-c/out.krml: $(AESGCM_AES256_NI_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir aesgcm-aes256-ni-c $(AESGCM_AES256_NI_FILES) -skip-translation

aesgcm-aes256-ni-c/Hacl_AES_256_GCM_NI.c: aesgcm-aes256-ni-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir aesgcm-aes256-ni-c  $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -add-include '"libintvector.h"' -drop Lib.IntVector.Intrinsics -bundle 'Hacl.AES_256_GCM.NI=*'

aesgcm-aes256-ni.exe: aesgcm-aes256-ni-c/Hacl_AES_256_GCM_NI.c aesgcm-ni-test.c
	$(CC) -march=native -mtune=native -O3 -I $(HACL_HOME)/lib/c -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . aesgcm-aes256-ni-c/Hacl_AES_256_GCM_NI.c $(KREMLIN_HOME)/kremlib/dist/generic/testlib.o aesgcm-aes256-ni-test.c -o aesgcm-aes256-ni.exe
	./aesgcm-aes256-ni.exe



aesgcm-m32-c/out.krml: $(AESGCM_M32_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir aesgcm-m32-c $(AESGCM_M32_FILES) -skip-translation

aesgcm-m32-c/Hacl_AES_128_GCM_M32.c: aesgcm-m32-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir aesgcm-m32-c  $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -drop Lib.IntVector.Intrinsics -bundle 'Hacl.AES_128_GCM.M32=*'

aesgcm-m32.exe: aesgcm-m32-c/Hacl_AES_128_GCM_M32.c aesgcm-m32-test.c
	$(CC) -march=native -mtune=native -O3 -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . aesgcm-m32-c/Hacl_AES_128_GCM_M32.c $(KREMLIN_HOME)/kremlib/dist/generic/testlib.o aesgcm-m32-test.c -o aesgcm-m32.exe
	./aesgcm-m32.exe


aesgcm-aes256-m32-c/out.krml: $(AESGCM_AES256_M32_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir aesgcm-aes256-m32-c $(AESGCM_AES256_M32_FILES) -skip-translation

aesgcm-aes256-m32-c/Hacl_AES_256_GCM_M32.c: aesgcm-aes256-m32-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir aesgcm-aes256-m32-c  $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -drop Lib.IntVector.Intrinsics -bundle 'Hacl.AES_256_GCM.M32=*'

aesgcm-aes256-m32.exe: aesgcm-aes256-m32-c/Hacl_AES_256_GCM_M32.c aesgcm-aes256-m32-test.c
	$(CC) -march=native -mtune=native -O3 -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . aesgcm-aes256-m32-c/Hacl_AES_256_GCM_M32.c $(KREMLIN_HOME)/kremlib/dist/generic/testlib.o aesgcm-aes256-m32-test.c -o aesgcm-aes256-m32.exe
	./aesgcm-aes256-m32.exe




aesgcm-perf: aesgcm-ni.exe  aesgcm-m32.exe aesgcm-aes256-ni.exe  aesgcm-aes256-m32.exe
	./aesgcm-ni.exe
	./aesgcm-m32.exe
	./aesgcm-aes256-ni.exe
	./aesgcm-aes256-m32.exe

test:
	rm -f .depend && $(MAKE) .depend
	$(MAKE) stage1
	STAGE=2 $(MAKE) stage2

stage1: $(GENERATED_DIR)/Makefile.include

stage2: $(OUT_DIR)/test.exe
	$(OUT_DIR)/test.exe

FSTAR_INCLUDE_DIRS = \
  $(HACL_KREMLIN) \
  $(KREMLIN_HOME)/kremlib \
  $(HACL_HOME)/specs \
  $(HACL_HOME)/lib \
  $(HACL_HOME)/lib/c

FSTAR_FLAGS = $(OTHERFLAGS) --cmi \
  --cache_checked_modules --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
  $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS)

ENABLE_HINTS = --use_hints --use_hint_hashes --record_hints --query_stats

ROOTS = Hacl.AES_128_GCM.NI.fst


.PRECIOUS: %.krml

.depend:
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar +FStar.UInt128 -LowStar -Spec' > $@

include .depend

# Admit SMT queries for modules in FStar, LowStar, and C
$(CACHE_DIR)/FStar.%.checked $(CACHE_DIR)/LowStar.%.checked $(CACHE_DIR)/C.%.checked: | .depend
	$(FSTAR) $< --admit_smt_queries true && \
	touch $@

$(CACHE_DIR)/%.checked: | .depend
	$(FSTAR) $< $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $<).hints && \
	touch $@

$(OUTPUT_DIR)/%.krml: | .depend
	$(FSTAR) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

# 2. Generation of .c files

KREMLIN_TESTLIB=-add-include '"dist/generic/TestLib.h"' $(KREMLIB)/dist/generic/testlib.c

KREMLIN=$(KREMLIN_HOME)/krml

# 2. Generation of .c files

# We use -drop (deprecated) only to avoid creating unnecessary .c,.h files
$(GENERATED_DIR)/Makefile.include: $(ALL_KRML_FILES) | .depend
	$(KREMLIN) $(KREMLIN_TESTLIB) -skip-compilation \
	-no-prefix 'Hacl.Test.SHA3' \
	-no-prefix 'Hacl.Impl.SHA3' \
	-no-prefix 'Hacl.SHA3' \
	-bundle 'Lib.*' \
	-bundle 'Spec.*' \
	-bundle 'C=C.Endianness' \
	-bundle 'Hacl.SHA3=Hacl.Impl.*,Hacl.SHA3' \
	-library 'C,FStar' \
	-drop 'LowStar,Spec,Prims,Lib,C.Loops.*' \
	-add-include '"c/Lib_PrintBuffer.h"' \
	-tmpdir $(GENERATED_DIR) \
	$^

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

# This is auto-generated by KreMLin; since the Makefile is staged via the
# inclusion of Makefile.include, the automated dependency analysis via $(CC) -MM
# also captures the dependencies between these files.
#
# KreMLin sees the fsti's for the various Lib* and LowStar modules and creates .h/.c
# files for them in $(GENERATED_DIR). However, we are only interested in the header,
# and drop these (mostly empty) C files.
ALL_OUR_FILES 	    = $(filter-out FStar_* Lib.c LowStar.c C.c, $(ALL_C_FILES))
ALL_GENERATED_FILES = $(addprefix $(GENERATED_DIR)/,$(ALL_OUR_FILES))

ALL_SOURCES = \
  $(ALL_GENERATED_FILES) \
  $(HACL_HOME)/lib/c/Lib_PrintBuffer.c

ALL_OBJS = $(patsubst %.c,%.o,$(ALL_SOURCES))

INCLUDE_DIRS = \
  $(KREMLIN_HOME)/include \
  $(KREMLIN_HOME)/kremlib \
  $(HACL_HOME)/lib

# TODO: remove -Wno-incompatible-pointer-types when issue with --cmi is fixed
CFLAGS += -O3 -march=native -mtune=native -funroll-loops
CFLAGS += $(addprefix -I ,$(INCLUDE_DIRS)) -Wall -Wextra -Werror \
  -Wno-parentheses -Wno-unused-parameter -Wno-unused-variable \
  -Wno-incompatible-pointer-types

# GNU Make manual section 4.14
%.d: %.c
	@set -e; rm -f $@; \
	  $(CC) -MM $(CFLAGS) $< > $@.$$$$; \
	  sed 's,\($(notdir $*)\)\.o[ :]*,$(dir $@)\1.o $@ : ,g' < $@.$$$$ > $@; \
	  rm -f $@.$$$$

-include $(patsubst %.c,%.d,$(ALL_SOURCES))

$(OUT_DIR):
	mkdir -p $@

$(OUT_DIR)/test.exe: $(ALL_OBJS) | $(OUT_DIR)
	$(info ALL_SOURCES is $(ALL_SOURCES))
	$(CC) $(CFLAGS) -o $@ $^ -L $(KREMLIN_HOME)/kremlib/out -lkremlib

.PRECIOUS: %.o

endif # STAGE=2

# 5. Targets for interactive mode

%.fst-in:
	@echo $(FSTAR_FLAGS) \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fst.hints

%.fsti-in:
	@echo $(FSTAR_FLAGS) \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fsti.hints

# 6. Clean targets

SHELL=/bin/bash

clean:
	rm -rf $(GENERATED_DIR) $(OUT_DIR)/*.exe $(OUT_DIR)/*.a
	rm -rf include/*.o include/*.d

clean-c:
	rm -rf $(GENERATED_DIR)/{*.{c,h},Makefile.include}

distclean: clean
	rm -rf $(OUT_DIR) $(CACHE_DIR) $(OUTPUT_DIR)
