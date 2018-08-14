FSTAR_HOME 	?= ../../../FStar
KREMLIN_HOME	?= ../../../kremlin
HACL_HOME	?= ../..
LWEKE_HOME	?= ../NIST/Reference_Implementation/reference/FrodoKEM-640

CACHE_DIR     = .cache
OUTPUT_DIR    = .output
HINT_DIR      = .hints
GENERATED_DIR = frodo-c
OUT_DIR       = frodo-c

# .checked files
# .krml files
# .hints
# .c, .h, .d
# .o, .a

KREMLIN_TESTLIB=-add-include '"extracted/TestLib.h"' $(KREMLIB)/c/testlib.c

KREMLIN=$(KREMLIN_HOME)/krml

# Manual staging...
all:
	sed -i.bak 's/params_n = size 640/params_n = size 64 /g' ../spec/Frodo.Params.fst
	rm -f .depend && $(MAKE) .depend
	$(MAKE) stage1
	STAGE=2 $(MAKE) stage2-test

lib:
	sed -i.bak 's/params_n = size 64 /params_n = size 640/g' ../spec/Frodo.Params.fst
	rm -f .depend && $(MAKE) .depend
	$(MAKE) stage1
	STAGE=2 RAND_OBJ=$(LWEKE_HOME)/objs/random/random.o $(MAKE) stage2-lib

stage1: $(GENERATED_DIR)/Makefile.include

stage2-test: $(OUT_DIR)/test.exe
	$(OUT_DIR)/test.exe

stage2-lib: $(OUT_DIR)/libfrodo_for_testing.a $(OUT_DIR)/libfrodo.a

KATs: $(OUT_DIR)/libfrodo_for_testing.a
	make -C $(LWEKE_HOME) USE_OPENSSL=FALSE GENERATION_A=CSHAKE128 KATS-fstar
	(cd $(LWEKE_HOME); frodo/PQCtestKAT_kem_cshake_fstar)

benchmark: $(OUT_DIR)/libfrodo.a
	make -C $(LWEKE_HOME) USE_OPENSSL=FALSE GENERATION_A=CSHAKE128 tests-fstar
	(cd $(LWEKE_HOME); frodo/test_KEM_fstar)

$(LWEKE_HOME)/%.o:
	make -C $(LWEKE_HOME) USE_OPENSSL=FALSE GENERATION_A=CSHAKE128 $*.o

# 1. Generation of .krml files
# - generate the F* dependency graph via `fstar --dep full`
# - verify every F* file in parallel to generate .checked files
# - extract each .checked file into a .krml file in parallel

FSTAR_INCLUDE_DIRS = \
  ../spec \
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


ROOTS = Hacl.Test.Frodo.fst

.PRECIOUS: %.krml

.depend:
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar +FStar.UInt128 -LowStar -Spec' > $@

include .depend

# Admit SMT queries for modules in FStar and LowStar namespaces
$(CACHE_DIR)/FStar.%.checked $(CACHE_DIR)/LowStar.%.checked $(CACHE_DIR)/C.%.checked: | .depend
	$(FSTAR) $< --admit_smt_queries true && \
	touch $@

$(CACHE_DIR)/prims.fst.checked $(CACHE_DIR)/Spec.Loops.fst.checked: | .depend
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

$(OUTPUT_DIR)/prims.krml $(OUTPUT_DIR)/Spec_Loops.krml $(OUTPUT_DIR)/Lib_IntTypes.krml: | .depend
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
	  $(HACL_HOME)/lib/c/Lib.Loops.fst \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

# 2. Generation of .c files

# We use -drop (deprecated) only to avoid creating unnecessary .c,.h files
$(GENERATED_DIR)/Makefile.include: $(ALL_KRML_FILES) | .depend
	$(KREMLIN) $(KREMLIN_TESTLIB) -skip-compilation \
	-no-prefix 'Hacl.Test.Frodo' \
	-no-prefix 'Hacl.Impl.Frodo.KEM' \
	-no-prefix 'Hacl.Frodo.Random' \
	-no-prefix 'Hacl.Frodo.Clear' \
	-bundle 'Hacl.Impl.Frodo.KEM=Frodo.Params,Hacl.Impl.*,Hacl.Frodo.*' \
	-bundle 'Lib.*' \
	-bundle 'Spec.*' \
	-bundle 'C=C.Endianness' \
	-library 'Hacl.Keccak,C,FStar' \
	-drop 'LowStar,Spec,Prims,Lib,C.Loops.*' \
	-add-include '"c/Lib_PQ_Print.h"' \
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
ALL_OUR_FILES 	    = $(filter-out FStar_* Lib.c LowStar.c Hacl_Keccak.c C.c, $(ALL_C_FILES))
ALL_GENERATED_FILES = $(addprefix $(GENERATED_DIR)/,$(ALL_OUR_FILES))

ALL_SOURCES = \
  $(ALL_GENERATED_FILES) \
  include/rng.c \
  include/random.c \
  include/Hacl_Keccak.c \
  include/clearwords.c \
  $(HACL_HOME)/lib/c/Lib_PQ_Print.c

ALL_OBJS = $(patsubst %.c,%.o,$(ALL_SOURCES)) \
	$(LWEKE_HOME)/objs/sha3/fips202.o \
	$(LWEKE_HOME)/objs/aes/aes_c.o \
	$(LWEKE_HOME)/objs/aes/aes.o

INCLUDE_DIRS = \
  $(KREMLIN_HOME)/include \
  $(KREMLIN_HOME)/kremlib \
  $(LWEKE_HOME)/sha3 \
  $(HACL_HOME)/lib

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

# 4. Collecting all of the object files into a static library.

$(OUT_DIR)/libfrodo_for_testing.a: $(filter-out $(OUT_DIR)/Hacl_Test_Frodo.o include/random.o, $(ALL_OBJS)) $(LWEKE_HOME)/tests/rng.o | $(OUT_DIR)
	$(AR) rcs -S $(OUT_DIR)/libfrodo_for_testing.a $^
	ranlib $(OUT_DIR)/libfrodo_for_testing.a

$(OUT_DIR)/libfrodo.a: $(filter-out $(OUT_DIR)/Hacl_Test_Frodo.o include/rng.o, $(ALL_OBJS)) $(LWEKE_HOME)/objs/random/random.o \
 | $(OUT_DIR)
	$(AR) rcs -S $(OUT_DIR)/libfrodo.a $^
	ranlib $(OUT_DIR)/libfrodo.a

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


# Old Makefile, simplified

ifeq ($(OLD),1)

GENERATED_DIR	= frodo-old
OUT_DIR	   	= frodo-old

INCLUDE_DIRS = \
  $(KREMLIN_HOME)/include \
  $(KREMLIN_HOME)/kremlib \
  $(LWEKE_HOME)/sha3 \
  $(HACL_HOME)/lib

CFLAGS += -O3 -march=native -mtune=native -funroll-loops
CFLAGS += $(addprefix -I ,$(INCLUDE_DIRS)) -Wall -Wextra -Werror \
  -Wno-parentheses -Wno-unused-parameter -Wno-unused-variable -Wno-infinite-recursion

BASE_OBJ = \
  ../../lib/c/Lib_PQ_Print.o \
  include/Hacl_Keccak.o \
  include/rng.o \
  include/clearwords.o \
  $(LWEKE_HOME)/objs/sha3/fips202.o \
  $(LWEKE_HOME)/tests/rng.o \
  $(LWEKE_HOME)/objs/aes/aes_c.o \
  $(LWEKE_HOME)/objs/aes/aes.o \
  $(OUT_DIR)/Hacl_Test_Frodo.o \
  $(OUT_DIR)/Hacl_Impl_Frodo_KEM.o

HACL_LIBS = \
  ../../lib/fst/Lib.IntTypes.fst \
  ../../lib/fst/Lib.RawIntTypes.fst \
  ../../lib/c/Lib.Loops.fst \
  ../../lib/fst/Lib.PQ.Buffer.fst

$(OUT_DIR)/out.krml: $(HACL_LIBS) Hacl.Impl.Matrix.fst Hacl.Keccak.fsti Hacl.Impl.Frodo.Params.fst Hacl.Impl.Frodo.Encode.fst Hacl.Impl.Frodo.Pack.fst Hacl.Impl.Frodo.Sample.fst Hacl.Impl.Frodo.Gen.fst Hacl.Impl.Frodo.KEM.fst Hacl.Test.Frodo.fst
	$(KREMLIN) -tmpdir $(OUT_DIR) \
	-I ../../specs -I ../spec -I ../../lib -I ../../lib/fst \
	-skip-translation $^

$(OUT_DIR)/Hacl_Impl_Frodo_KEM.c $(OUT_DIR)/Hacl_Test_Frodo.c: $(OUT_DIR)/out.krml
	$(KREMLIN) $(KREMLIN_TESTLIB) -skip-compilation \
	-no-prefix 'Hacl.Test.Frodo' \
	-no-prefix 'Hacl.Impl.Frodo.KEM' \
	-no-prefix 'Hacl.Frodo.Random' \
	-no-prefix 'Hacl.Frodo.Clear' \
	-bundle 'Hacl.Impl.Frodo.KEM=Frodo.Params,Hacl.Impl.*,Hacl.Frodo.*' \
	-bundle 'Lib.*' \
	-bundle 'Spec.*' \
	-bundle 'C=C.Endianness' \
	-library 'Hacl.Keccak,C,FStar' \
	-drop 'LowStar,Spec,Prims,Lib,C.Loops.*' \
	-add-include '"c/Lib_PQ_Print.h"' \
	-tmpdir $(GENERATED_DIR) \
	$^

$(OUT_DIR)/test.exe: $(BASE_OBJ)
	$(CC) $(CFLAGS) -o $@ $^ -L $(KREMLIN_HOME)/kremlib/out -lkremlib

test: $(OUT_DIR)/test.exe
	$(OUT_DIR)/test.exe

endif
