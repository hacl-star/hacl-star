FSTAR_HOME   ?= ../../../../FStar
KREMLIN_HOME ?= ../../../../kremlin
HACL_HOME    ?= ../../..

CACHE_DIR     ?= $(HACL_HOME)/.cache
OUTPUT_DIR    ?= .output
HINT_DIR      ?= $(HACL_HOME)/.hints
GENERATED_DIR ?= gf128-c
OUT_DIR	      ?= gf128-c

.PHONY: all test stage1 stage2 clean clean-c distclean

all: test

test:
	rm -f .depend && $(MAKE) .depend
	$(MAKE) stage1
	STAGE=2 $(MAKE) stage2

stage1: $(GENERATED_DIR)/Hacl_Gf128_NI.c \
	$(GENERATED_DIR)/Hacl_Gf128_PreComp.c

stage2: gf128-ni.exe gf128-precomp.exe
	./gf128-ni.exe
	./gf128-precomp.exe

FSTAR_INCLUDE_DIRS = \
  $(HACL_KREMLIN) \
  $(KREMLIN_HOME)/kremlib \
  $(HACL_HOME)/specs \
  $(HACL_HOME)/lib \
  $(HACL_HOME)/lib/c 

FSTAR_FLAGS = $(OTHERFLAGS) --cmi \
  --cache_checked_modules --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
  --already_cached "'Prims+FStar+LowStar+C+Spec.Loops+TestLib+Lib'" \
  $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS)

ENABLE_HINTS = --use_hints --use_hint_hashes --record_hints --query_stats

ROOTS = Hacl.Gf128.NI.fst Hacl.Gf128.PreComp.fst

.PRECIOUS: %.krml

.depend:
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar +FStar.UInt128 -LowStar -Spec' > $@

include .depend

$(HINT_DIR):
	mkdir -p $@

$(CACHE_DIR):
	mkdir -p $@

%.checked: | .depend $(HINT_DIR) $(CACHE_DIR)
	$(FSTAR) $< $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $*).hints && \
	touch -c $@

$(OUTPUT_DIR)/%.krml: | .depend
	$(FSTAR) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

# 2. Generation of .c files

KREMLIN_TESTLIB=-fbuiltin-uint128 -fnocompound-literals -fparentheses -fcurly-braces \
	-funroll-loops 8 -warn-error +9 -add-include '"kremlib.h"' $(KREMLIB)/dist/minimal/testlib.c

KREMLIN=$(KREMLIN_HOME)/krml

# 2. Generation of .c files

# We use -drop (deprecated) only to avoid creating unnecessary .c,.h files
$(GENERATED_DIR)/Hacl_Gf128_NI.c: $(ALL_KRML_FILES) | .depend
	$(KREMLIN) $(KREMLIN_TESTLIB) -add-include '"libintvector.h"' -skip-compilation \
	-bundle 'Lib.*' \
	-bundle 'Spec.*' \
	-bundle 'Hacl.Gf128.NI=Hacl.Impl.*,Hacl.Gf128.NI' \
	-drop 'Lib.IntVector.Intrinsics,FStar.UInt128,LowStar,Spec,Prims,Lib,C.Loops.*,C.*,C,FStar.*,Hacl.Spec.*,Hacl.Gf128.PreComp' \
	-tmpdir $(GENERATED_DIR) \
	$^


$(GENERATED_DIR)/Hacl_Gf128_PreComp.c: $(ALL_KRML_FILES) | .depend
	$(KREMLIN) $(KREMLIN_TESTLIB) -skip-compilation \
	-bundle 'Lib.*' \
	-bundle 'Spec.*' \
	-bundle 'Hacl.Gf128.PreComp=Hacl.Impl.*,Hacl.Gf128.PreComp' \
	-drop 'Lib.IntVector.Intrinsics,FStar.UInt128,LowStar,Spec,Prims,Lib,C.Loops.*,C.*,C,FStar.*,Hacl.Spec.*,Hacl.Gf128.NI' \
	-tmpdir $(GENERATED_DIR) \
	$^

# The Makefile is manually staged because GNU Make does not understand
# dependencies between the Makefiles we include, i.e. it won't first generate
# the .depend, parse it, then generate Makefile.include, parse it, then
# generate dependencies among the C files
ifeq ($(STAGE),2)

# 3. Collecting all of our source files, and generating corresponding object
# files.

INCLUDE_DIRS = \
  $(KREMLIN_HOME)/include \
  $(KREMLIN_HOME)/kremlib \
  $(KREMLIN_HOME)/kremlib/c \
  $(KREMLIN_HOME)/kremlib/dist/minimal \
  $(HACL_HOME)/lib \
  $(HACL_HOME)/lib/c

CFLAGS += -O3 -march=native -mtune=native -funroll-loops
CFLAGS += $(addprefix -I ,$(INCLUDE_DIRS)) -Wall -Wextra -Werror \
  -Wno-parentheses -Wno-unused-parameter -Wno-unused-variable


gf128-precomp.exe: $(GENERATED_DIR)/Hacl_Gf128_PreComp.c
	$(CC) -march=native -mtune=native -O3 -I $(KREMLIN_HOME)/kremlib/dist/generic -I $(KREMLIN_HOME)/include -I . $(GENERATED_DIR)/Hacl_Gf128_PreComp.c $(KREMLIN_HOME)/kremlib/dist/generic/testlib.o gf128-precomp-test.c -o gf128-precomp.exe
	./gf128-precomp.exe

gf128-ni.exe: $(GENERATED_DIR)/Hacl_Gf128_NI.c
	$(CC) -march=native -mtune=native -O3 -I $(KREMLIN_HOME)/kremlib/dist/generic -I $(KREMLIN_HOME)/include -I $(HACL_HOME)/lib/c -I . $(GENERATED_DIR)/Hacl_Gf128_NI.c $(KREMLIN_HOME)/kremlib/dist/generic/testlib.o gf128-ni-test.c -o gf128-ni.exe
	./gf128-ni.exe


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

clean-c:
	rm -rf $(GENERATED_DIR)/{*.{c,h},Makefile.include}

distclean: clean
	rm -rf $(OUT_DIR) $(OUTPUT_DIR) *.checked
