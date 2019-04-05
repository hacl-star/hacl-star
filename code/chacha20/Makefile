FSTAR_HOME   ?= ../../../../FStar
KREMLIN_HOME ?= ../../../../kremlin
HACL_HOME    ?= ../../..

OUTPUT_DIR    = .output
HINT_DIR      = .hints
GENERATED_DIR = chacha20-c
OUT_DIR	      = chacha20-c

.PHONY: all test stage1 stage2 clean clean-c distclean

all: chacha20-vec-perf

verify: test

#CC=clang-7
CC=gcc

CHACHA20_FILES= $(HACL_HOME)/lib/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/Lib.RawIntTypes.fst \
	$(HACL_HOME)/lib/Lib.Buffer.fst \
	$(HACL_HOME)/lib/Lib.ByteBuffer.fst \
	$(HACL_HOME)/lib/Lib.Loops.fst \
	Hacl.Impl.Chacha20.Core32.fst \
	Hacl.Impl.Chacha20.fst \
	Hacl.Chacha20.fst 

KREMLIN_ARGS:=-funroll-loops 8 -warn-error +9 -I $(HACL_HOME)/lib/ -I $(KREMLIN_HOME)/kremlib -I $(HACL_HOME)/specs -I . -ccopt '-march=native' -fbuiltin-uint128 -bundle Prims -bundle FStar -drop Prims -drop FStar -drop FStar.UInt128 -fnocompound-literals -fc89-scope -fparentheses -fcurly-braces -dast

chacha20-c/out.krml: $(CHACHA20_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha20-c $(CHACHA20_FILES) -skip-translation 

chacha20-c/Hacl_Chacha20.c: chacha20-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha20-c  $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -bundle 'Hacl.Chacha20=*'

chacha20.exe: chacha20-c/Hacl_Chacha20.c chacha20-c/out.krml
	$(CC) -march=native -mtune=native -O3 -I $(KREMLIN_HOME)/kremlib/dist/generic -I $(KREMLIN_HOME)/include -I . chacha20-c/Hacl_Chacha20.c $(KREMLIN_HOME)/kremlib/dist/generic/testlib.o $(HACL_HOME)/snapshots/hacl-c/Hacl_Chacha20.c chacha20-test.c -o chacha20.exe 
	./chacha20.exe

chacha20-perf: chacha20.exe


CHACHA20_VEC_FILES= $(HACL_HOME)/lib/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/Lib.RawIntTypes.fst \
	$(HACL_HOME)/lib/Lib.Buffer.fst \
	$(HACL_HOME)/lib/Lib.ByteBuffer.fst \
	$(HACL_HOME)/lib/Lib.IntVector.Intrinsics.fsti \
	$(HACL_HOME)/lib/Lib.IntVector.fst \
	$(HACL_HOME)/lib/Lib.Loops.fst \
	Hacl.Impl.Chacha20.Core32xN.fst \
	Hacl.Impl.Chacha20.Vec.fst 

KREMLIN_ARGS:=-funroll-loops 8 -warn-error +9 -I $(HACL_HOME)/lib/ -I $(HACL_HOME)/lib/c -I $(KREMLIN_HOME)/kremlib -I $(HACL_HOME)/specs -I . -ccopt '-march=native' -fbuiltin-uint128 -bundle Prims -bundle FStar -drop Prims -drop FStar -drop FStar.UInt128 -fnocompound-literals -fc89-scope -fparentheses -fcurly-braces -drop Lib.IntVector.Intrinsics

chacha20-vec32-c/out.krml: $(CHACHA20_VEC_FILES) Hacl.Chacha20.Vec32.fst
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha20-vec32-c $^ -skip-translation 

chacha20-vec32-c/Hacl_Chacha20_Vec32.c: chacha20-vec32-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha20-vec32-c  $^ -skip-compilation \
	   -minimal -add-include '"vec-intrin.h"' -add-include '"kremlib.h"' -bundle 'Hacl.Chacha20_Vec32=*'

chacha20-vec128-c/out.krml: $(CHACHA20_VEC_FILES) Hacl.Chacha20.Vec128.fst
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha20-vec128-c $^ -skip-translation 

chacha20-vec128-c/Hacl_Chacha20_Vec128.c: chacha20-vec128-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha20-vec128-c  $^ -skip-compilation \
	   -minimal -add-include '"vec-intrin.h"' -add-include '"kremlib.h"' -bundle 'Hacl.Chacha20_Vec128=*'

chacha20-vec256-c/out.krml: $(CHACHA20_VEC_FILES) Hacl.Chacha20.Vec256.fst
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha20-vec256-c $^ -skip-translation 

chacha20-vec256-c/Hacl_Chacha20_Vec256.c: chacha20-vec256-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha20-vec256-c  $^ -skip-compilation \
	   -minimal -add-include '"vec-intrin.h"' -add-include '"kremlib.h"' -bundle 'Hacl.Chacha20_Vec256=*'


chacha20-vec.exe: chacha20-vec32-c/Hacl_Chacha20_Vec32.c chacha20-vec128-c/Hacl_Chacha20_Vec128.c chacha20-vec256-c/Hacl_Chacha20_Vec256.c
	$(CC) -march=native -mtune=native -O3 -I $(KREMLIN_HOME)/kremlib/dist/generic -I $(KREMLIN_HOME)/include -I $(HACL_HOME)/lib/c -I . chacha20-vec32-c/Hacl_Chacha20_Vec32.c chacha20-vec128-c/Hacl_Chacha20_Vec128.c chacha20-vec256-c/Hacl_Chacha20_Vec256.c $(HACL_HOME)/snapshots/hacl-c/Hacl_Chacha20.c $(HACL_HOME)/snapshots/hacl-c/Hacl_Chacha20_Vec128.c chacha20-vec-test.c -o chacha20-vec.exe $(KREMLIN_HOME)/kremlib/dist/generic/testlib.o 
	./chacha20-vec.exe


# chacha20-vec.exe: chacha20-vec32-c/Hacl_Chacha20_Vec32.c chacha20-vec128-c/Hacl_Chacha20_Vec128.c chacha20-vec256-c/Hacl_Chacha20_Vec256.c
# 	$(CC) -march=native -mtune=native -O3 -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I $(HACL_HOME)/lib/c -I . chacha20-vec32-c/Hacl_Chacha20_Vec32.c chacha20-vec128-c/Hacl_Chacha20_Vec128.c chacha20-vec256-c/Hacl_Chacha20_Vec256.c $(HACL_HOME)/snapshots/hacl-c/Hacl_Chacha20.c $(HACL_HOME)/snapshots/hacl-c/Hacl_Chacha20_Vec128.c chacha20-vec-test.c -o chacha20-vec.exe $(KREMLIN_HOME)/kremlib/dist/generic/testlib.o -ldl -lpthread -I ../boringssl/include ../boringssl/build/crypto/libcrypto.a
# 	./chacha20-vec.exe

chacha20-vec-perf: chacha20-vec.exe


test:
	rm -f .depend && $(MAKE) .depend
	$(MAKE) stage1
	STAGE=2 $(MAKE) stage2

stage1: # $(GENERATED_DIR)/Makefile.include

stage2: verify-all
# stage2: $(OUT_DIR)/test.exe
# 	$(OUT_DIR)/test.exe

FSTAR_INCLUDE_DIRS = \
  $(HACL_KREMLIN) \
  $(KREMLIN_HOME)/kremlib \
  $(HACL_HOME)/specs \
  $(HACL_HOME)/lib

FSTAR_FLAGS = $(OTHERFLAGS) --cmi \
  --cache_checked_modules --odir $(OUTPUT_DIR) \
  --already_cached "'Prims+FStar+LowStar+C+Spec.Loops+TestLib+Lib'" \
  $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS)

ENABLE_HINTS = --use_hints --use_hint_hashes --record_hints --query_stats

ROOTS = Hacl.Chacha20.fst Hacl.Chacha20.Vec.fst

.PRECIOUS: %.krml

.depend:
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar +FStar.UInt128 -LowStar' > $@

include .depend

$(HINT_DIR):
	mkdir -p $@

%.checked: | .depend $(HINT_DIR)
	$(FSTAR) $< $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $*).hints && \
	touch -c $@

verify-all: $(addsuffix .checked,$(ALL_FST_FILES))
	$(info $(addsuffix .checked,$(ALL_FST_FILES)))

# $(OUTPUT_DIR)/%.krml: | .depend
# 	$(FSTAR) --codegen Kremlin \
# 	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
# 	  $(notdir $(subst .checked,,$<)) && \
# 	touch $@

# 2. Generation of .c files

KREMLIN_TESTLIB=-add-include '"extracted/TestLib.h"' $(KREMLIB)/dist/generic/testlib.c

KREMLIN=$(KREMLIN_HOME)/krml

# # 2. Generation of .c files

# # We use -drop (deprecated) only to avoid creating unnecessary .c,.h files
# $(GENERATED_DIR)/Makefile.include: $(ALL_KRML_FILES) | .depend
# 	$(KREMLIN) $(KREMLIN_TESTLIB) -skip-compilation \
# 	-no-prefix 'Hacl.Test.Chacha20' \
# 	-no-prefix 'Hacl.Impl.Chacha20' \
# 	-no-prefix 'Hacl.Chacha20' \
# 	-bundle 'Lib.*' \
# 	-bundle 'Spec.*' \
# 	-bundle 'C=C.Endianness' \
# 	-bundle 'Hacl.Chacha20=Hacl.Impl.*,Hacl.Chacha20' \
# 	-library 'C,FStar' \
# 	-drop 'LowStar,Spec,Prims,Lib,C.Loops.*' \
# 	-tmpdir $(GENERATED_DIR) \
# 	$^

# # The Makefile is manually staged because GNU Make does not understand
# # dependencies between the Makefiles we include, i.e. it won't first generate
# # the .depend, parse it, then generate Makefile.include, parse it, then
# # generate dependencies among the C files
# ifeq ($(STAGE),2)

# # The top-level invocation guarantees that stage1 has been run and this file is
# # there.
# include $(GENERATED_DIR)/Makefile.include

# # 3. Collecting all of our source files, and generating corresponding object
# # files.

# # This is auto-generated by KreMLin; since the Makefile is staged via the
# # inclusion of Makefile.include, the automated dependency analysis via $(CC) -MM
# # also captures the dependencies between these files.
# #
# # KreMLin sees the fsti's for the various Lib* and LowStar modules and creates .h/.c
# # files for them in $(GENERATED_DIR). However, we are only interested in the header,
# # and drop these (mostly empty) C files.
# ALL_OUR_FILES 	    = $(filter-out FStar_* Lib.c LowStar.c C.c, $(ALL_C_FILES))
# ALL_GENERATED_FILES = $(addprefix $(GENERATED_DIR)/,$(ALL_OUR_FILES))

# ALL_SOURCES = \
#   $(ALL_GENERATED_FILES) \
#   $(HACL_HOME)/lib/c/Lib_PrintBuffer.c

# ALL_OBJS = $(patsubst %.c,%.o,$(ALL_SOURCES))

# INCLUDE_DIRS = \
#   $(KREMLIN_HOME)/include \
#   $(KREMLIN_HOME)/kremlib \
#   $(KREMLIN_HOME)/kremlib/dist/generic \
#   $(HACL_HOME)/lib

# # TODO: remove -Wno-incompatible-pointer-types when issue with --cmi is fixed
# CFLAGS += -O3 -march=native -mtune=native -funroll-loops
# CFLAGS += $(addprefix -I ,$(INCLUDE_DIRS)) -Wall -Wextra -Werror \
#   -Wno-parentheses -Wno-unused-parameter -Wno-unused-variable \
#   -Wno-incompatible-pointer-types

# # GNU Make manual section 4.14
# %.d: %.c
# 	@set -e; rm -f $@; \
# 	  $(CC) -MM $(CFLAGS) $< > $@.$$$$; \
# 	  sed 's,\($(notdir $*)\)\.o[ :]*,$(dir $@)\1.o $@ : ,g' < $@.$$$$ > $@; \
# 	  rm -f $@.$$$$

# -include $(patsubst %.c,%.d,$(ALL_SOURCES))

# $(OUT_DIR):
# 	mkdir -p $@

# $(OUT_DIR)/test.exe: $(ALL_OBJS) | $(OUT_DIR)
# 	$(info ALL_SOURCES is $(ALL_SOURCES))
# 	$(CC) $(CFLAGS) -o $@ $^ -L $(KREMLIN_HOME)/kremlib/dist/generic -lkremlib

# .PRECIOUS: %.o

# endif # STAGE=2

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
	rm -rf $(OUT_DIR) $(OUTPUT_DIR) *.checked
