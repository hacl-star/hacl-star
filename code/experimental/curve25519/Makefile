FSTAR_HOME   ?= ../../../../FStar
KREMLIN_HOME ?= ../../../../kremlin
HACL_HOME    ?= ../../..

CACHE_DIR     = .cache
OUTPUT_DIR    = .output
HINT_DIR      = .hints
GENERATED_DIR = x25519-c
OUT_DIR	      = x25519-c

.PHONY: all test stage1 stage2 clean clean-c distclean

all: curve25519_51.exe curve25519_64.exe

verify: test

CC=/usr/local/Cellar/llvm/7.0.0/bin/clang-7
#CC=gcc-8

CURVE25519_FILES= $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/fst/Lib.RawIntTypes.fst \
	$(HACL_HOME)/lib/fst/Lib.Buffer.fst \
	$(HACL_HOME)/lib/fst/Lib.ByteBuffer.fst \
	$(HACL_HOME)/lib/c/Lib.Loops.fst \
	Hacl.Impl.Curve25519.Field26.fst \
	Hacl.Impl.Curve25519.Field64.fst \
	Hacl.Impl.Curve25519.Field51.fst \
	Hacl.Impl.Curve25519.Fields.fst \
	Hacl.Impl.Curve25519.Generic.fst 

KREMLIN_ARGS:=-funroll-loops 8 -warn-error +9 -I $(HACL_HOME)/lib/ -I $(HACL_HOME)/lib/fst -I $(KREMLIN_HOME)/kremlib -I $(HACL_HOME)/specs -I ./lemmas -I . -ccopt '-march=native' -fbuiltin-uint128 -drop FStar.UInt128 -fnocompound-literals -fc89-scope -fparentheses -fcurly-braces

curve51-c/out.krml: $(CURVE25519_FILES) Hacl.Curve25519_51.fst
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir curve51-c $(CURVE25519_FILES) Hacl.Curve25519_51.fst -skip-translation 

curve51-c/Hacl_Curve25519_51.c: curve51-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir curve51-c  $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -bundle 'Hacl.Curve25519_51=*'

curve26-c/out.krml: $(CURVE25519_FILES) Hacl.Curve25519_26.fst
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir curve26-c $(CURVE25519_FILES) Hacl.Curve25519_26.fst -skip-translation 

curve26-c/Hacl_Curve25519_26.c: curve26-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir curve26-c  $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -bundle 'Hacl.Curve25519_26=*'

curve64-c/out.krml: $(CURVE25519_FILES) Hacl.Curve25519_64.fst
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir curve64-c $(CURVE25519_FILES) Hacl.Curve25519_64.fst -drop Hacl.Impl.Curve25519.Field64.Core -no-prefix  Hacl.Impl.Curve25519.Field64.Core -skip-translation 

curve64-c/Hacl_Curve25519_64.c: curve64-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir curve64-c  $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -bundle 'Hacl.Curve25519_64=*' -drop Hacl.Impl.Curve25519.Field64.Core -no-prefix  Hacl.Impl.Curve25519.Field64.Core -add-include '"vale_25519.h"'

curve25519_51.exe: curve51-c/Hacl_Curve25519_51.c
	$(CC) -march=native -mtune=native -O3 -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . curve51-c/Hacl_Curve25519_51.c $(KREMLIN_HOME)/kremlib/c/testlib.o curve51-test.c -o curve25519_51.exe
	./curve25519_51.exe

curve25519_26.exe: curve26-c/Hacl_Curve25519_26.c
	$(CC) -march=native -mtune=native -O3 -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . curve26-c/Hacl_Curve25519_26.c $(KREMLIN_HOME)/kremlib/c/testlib.o curve26-test.c -o curve25519_26.exe
	./curve25519_26.exe


curve25519_64_vale.exe: curve64-c/Hacl_Curve25519_64.c vale_25519.h vale/obj/curve25519-x86_64-darwin.S
	$(CC) -march=native -mtune=native -flto -O3 vale/obj/curve25519-x86_64-darwin.S -c -o vale25519.o 
	$(CC) -march=native -mtune=native -flto -O3 -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . curve64-c/Hacl_Curve25519_64.c $(KREMLIN_HOME)/kremlib/c/testlib.o curve64-test.c -o curve25519_64_vale.exe vale25519.o 
	./curve25519_64_vale.exe

curve25519_64_v_inline.exe: curve64-c/Hacl_Curve25519_64.c rfc7748_25519.h
	cp -f vale_25519.h tmp_25519.h
	cp -f vale-inline.h vale_25519.h
	$(CC) -march=native -mtune=native -O3 -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . curve64-c/Hacl_Curve25519_64.c $(KREMLIN_HOME)/kremlib/c/testlib.o curve64-test.c -o curve25519_64_v_inline.exe 
	cp -f tmp_25519.h vale_25519.h
	./curve25519_64_v_inline.exe

curve25519_64_mixed.exe: curve64-c/Hacl_Curve25519_64.c rfc7748_25519.h
	cp -f vale_25519.h tmp_25519.h
	cp -f rfc7748_25519.h vale_25519.h
	$(CC) -march=native -mtune=native -O3 -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . curve64-c/Hacl_Curve25519_64.c $(KREMLIN_HOME)/kremlib/c/testlib.o curve64-test.c -o curve25519_64_mixed.exe 
	cp -f tmp_25519.h vale_25519.h
	./curve25519_64_mixed.exe

curve25519_64_rfc.exe: curve64-c/Hacl_Curve25519_64.c
	$(CC) -march=native -mtune=native -O3 -I rfc7748_src/ rfc7748_src/fp25519_x64.c -c -o fp25519.o 
	$(CC) -march=native -mtune=native -O3 -I rfc7748_src/ rfc7748_src/x25519_x64.c -c -o x25519.o 
	$(CC) -march=native -mtune=native -O3 -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . $(KREMLIN_HOME)/kremlib/c/testlib.o curve64-rfc-test.c -o curve25519_64_rfc.exe fp25519.o x25519.o
	./curve25519_64_rfc.exe

curve25519_64.exe: curve25519_64_vale.exe curve25519_64_mixed.exe curve25519_64_rfc.exe
	./curve25519_64_vale.exe
	./curve25519_64_rfc.exe
	./curve25519_64_mixed.exe

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
  $(HACL_HOME)/lib/fst \
  $(HACL_HOME)/lib/c

FSTAR_FLAGS = $(OTHERFLAGS) --cmi \
  --cache_checked_modules --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
  $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS)

ENABLE_HINTS = --use_hints --use_hint_hashes --record_hints --query_stats

ROOTS = Hacl.Curve25519_51.fst


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

KREMLIN_TESTLIB=-add-include '"extracted/TestLib.h"' $(KREMLIB)/c/testlib.c

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
