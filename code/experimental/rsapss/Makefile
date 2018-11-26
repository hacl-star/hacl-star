FSTAR_HOME   ?= ../../../../FStar
KREMLIN_HOME ?= ../../../../kremlin
HACL_HOME    ?= ../../..

CACHE_DIR     = .cache
OUTPUT_DIR    = .output
HINT_DIR      = .hints
GENERATED_DIR = rsapss-c
OUT_DIR	      = rsapss-c

KREMLIN_TESTLIB=-add-include '"extracted/TestLib.h"' $(KREMLIB)/c/testlib.c

KREMLIN=$(KREMLIN_HOME)/krml

all: test

test:
	rm -f .depend && $(MAKE) .depend
	$(MAKE) stage1
	STAGE=2 $(MAKE) stage2-test

stage1: $(GENERATED_DIR)/Makefile.include

stage2-test: $(OUT_DIR)/test.exe
	$(OUT_DIR)/test.exe

FSTAR_INCLUDE_DIRS = \
  $(HACL_KREMLIN) \
  $(KREMLIN_HOME)/kremlib \
  $(HACL_HOME)/specs \
  $(HACL_HOME)/lib \
  $(HACL_HOME)/lib/fst \
  $(HACL_HOME)/lib/c

FSTAR_INCLUDES = $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(OTHERFLAGS) \
  --cache_checked_modules --cache_dir $(CACHE_DIR) \
  --odir $(OUTPUT_DIR) $(FSTAR_INCLUDES)

FSTARR = $(FSTAR_HOME)/bin/fstar.exe $(OTHERFLAGS) \
  --cache_dir $(CACHE_DIR) \
  --odir $(OUTPUT_DIR) $(FSTAR_INCLUDES)

ENABLE_HINTS = --use_hints --use_hint_hashes --record_hints --query_stats

%.fst-in:
	@echo --cache_checked_modules --cache_dir $(CACHE_DIR) \
	$(FSTAR_INCLUDES) \
	$(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fst.hints

%.fsti-in:
	@echo --cache_checked_modules --cache_dir $(CACHE_DIR) \
	$(FSTAR_INCLUDES) \
	$(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fsti.hints

ROOTS = Hacl.Test.RSA.fst

.PRECIOUS: %.krml

.depend:
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar +FStar.UInt128 -LowStar -Spec' > $@

include .depend

# Admit SMT queries for modules in FStar, LowStar, C, and Spec namespaces
$(CACHE_DIR)/FStar.%.checked $(CACHE_DIR)/LowStar.%.checked $(CACHE_DIR)/C.%.checked: | .depend
	$(FSTAR) $< --admit_smt_queries true && \
	touch $@

$(CACHE_DIR)/prims.fst.checked $(CACHE_DIR)/Spec.Loops.fst.checked $(CACHE_DIR)/Spec.Keccak.fst.checked: | .depend
	$(FSTAR) $< --admit_smt_queries true && \
	touch $@

$(CACHE_DIR)/Lib.RawIntTypes.fst.checked: $(CACHE_DIR)/Lib.IntTypes.fst.checked
$(CACHE_DIR)/Lib.RawIntTypes.fst.checked: | .depend
	$(FSTARR) $< \
	  --expose_interfaces \
	  $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $<).hints && \
	touch $@

$(CACHE_DIR)/%.checked: | .depend
	$(FSTAR) $< \
	  $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $<).hints && \
	touch $@

# We mimick what Kremlin would do when it is driving F* and it is given all
# .fst in the command-line: it would add `--expose_interfaces` and expose all
# implementations.
#
# We need to additionally expose Lib.Loops and Lib.RawIntTypes for the
# compilation to succeed and be as if Kremlin was given all files at the
# same time. This means stale cache files, so we use --lax

$(OUTPUT_DIR)/FStar_%.krml $(OUTPUT_DIR)/LowStar_%.krml $(OUTPUT_DIR)/C%.krml: | .depend
	$(FSTARR) --codegen Kremlin --lax \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

$(OUTPUT_DIR)/prims.krml $(OUTPUT_DIR)/Spec_Loops.krml $(OUTPUT_DIR)/Lib_IntTypes.krml $(OUTPUT_DIR)/Lib_ByteBuffer.krml: | .depend
	$(FSTARR) --codegen Kremlin --lax \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

$(OUTPUT_DIR)/Lib_RawIntTypes.krml: $(OUTPUT_DIR)/Lib_IntTypes.krml
$(OUTPUT_DIR)/Lib_RawIntTypes.krml: | .depend
	$(FSTAR) --codegen Kremlin --lax \
	  --expose_interfaces \
	  $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

$(OUTPUT_DIR)/Lib_Loops.krml: | .depend $(OUTPUT_DIR)/Lib_RawIntTypes.krml
	$(FSTAR) --codegen Kremlin --lax \
	  --expose_interfaces \
	  $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	  $(HACL_HOME)/lib/fst/Lib.RawIntTypes.fst \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

$(OUTPUT_DIR)/%.krml: | .depend $(OUTPUT_DIR)/Lib_RawIntTypes.krml
	$(FSTAR) --codegen Kremlin --lax \
	  --expose_interfaces \
	  $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	  $(HACL_HOME)/lib/fst/Lib.RawIntTypes.fst \
	  $(HACL_HOME)/lib/fst/Lib.ByteBuffer.fst \
	  $(HACL_HOME)/lib/c/Lib.Loops.fst \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

# 2. Generation of .c files

# We use -drop (deprecated) only to avoid creating unnecessary .c,.h files
$(GENERATED_DIR)/Makefile.include: $(ALL_KRML_FILES) | .depend
	$(KREMLIN) $(KREMLIN_TESTLIB) -skip-compilation \
	-no-prefix 'Hacl.Test.RSA' \
	-no-prefix 'Hacl.Impl.RSA' \
	-no-prefix 'Hacl.RSAPSS' \
	-bundle 'Lib.*' \
	-bundle 'Spec.*' \
	-bundle 'C=C.Endianness' \
	-bundle 'Hacl.RSAPSS=Hacl.Impl.*,Hacl.RSAPSS' \
	-library 'Hacl.SHA256,C,FStar' \
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
ALL_OUR_FILES 	    = $(filter-out FStar_* Lib.c LowStar.c C.c Hacl_SHA256.c, $(ALL_C_FILES))
ALL_GENERATED_FILES = $(addprefix $(GENERATED_DIR)/,$(ALL_OUR_FILES))

ALL_SOURCES = \
  $(ALL_GENERATED_FILES) \
  $(HACL_HOME)/lib/c/Lib_PrintBuffer.c \
  include/Hacl_SHA256.c \
  $(HACL_HOME)/snapshots/hacl-c/Hacl_SHA2_256.c

ALL_OBJS = $(patsubst %.c,%.o,$(ALL_SOURCES))

INCLUDE_DIRS = \
  $(KREMLIN_HOME)/include \
  $(KREMLIN_HOME)/kremlib \
  $(HACL_HOME)/lib \
  $(HACL_HOME)/snapshots/hacl-c

CFLAGS += -O3 -march=native -mtune=native -funroll-loops
CFLAGS += $(addprefix -I ,$(INCLUDE_DIRS)) -Wall -Wextra -Werror \
  -Wno-parentheses -Wno-unused-parameter -Wno-unused-variable -Wno-infinite-recursion

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

endif # COMPILE

# 5. Clean targets that do not re-trigger anything except perhaps the generation
# of the .depend file.

SHELL=/bin/bash

.PHONY: clean
clean:
	rm -rf $(GENERATED_DIR) $(OUT_DIR)/*.exe $(OUT_DIR)/*.a
	rm -rf include/*.o include/*.d

.PHONY: clean-c
clean-c:
	rm -rf $(GENERATED_DIR)/{*.{c,h},Makefile.include}

.PHONY: distclean
distclean: clean
	rm -rf $(OUT_DIR) $(CACHE_DIR) $(OUTPUT_DIR)
