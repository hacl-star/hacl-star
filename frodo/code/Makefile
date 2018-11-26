FSTAR_HOME   ?= ../../../FStar
KREMLIN_HOME ?= ../../../kremlin
HACL_HOME    ?= ../..

VARIANT      ?= 64-cSHAKE

ifeq ($(VARIANT),64-cSHAKE)
  KEM_DIR = FrodoKEM-640
  GENERATION_A = CSHAKE128
else ifeq ($(VARIANT),640-cSHAKE)
  KEM_DIR = FrodoKEM-640
  GENERATION_A = CSHAKE128
else ifeq ($(VARIANT),640-AES)
  KEM_DIR = FrodoKEM-640
  GENERATION_A = AES128
  ifeq ($(TARGET),)
    $(error ERROR: We only support TARGET=x64 for AES variants)
  endif
else ifeq ($(VARIANT),976-cSHAKE)
  KEM_DIR = FrodoKEM-976
  GENERATION_A = CSHAKE128
else ifeq ($(VARIANT),976-AES)
  KEM_DIR = FrodoKEM-976
  GENERATION_A = AES128
  ifeq ($(TARGET),)
    $(error ERROR: We only support TARGET=x64 for AES variants)
  endif
else
  $(error ERROR: VARIANT must be one of {640,976}-{cSHAKE,AES}, or 64-cSHAKE)
endif

UNAME = $(shell uname)
ifeq ($(UNAME),Darwin)
  ARCH	= -Darwin
else ifeq ($(UNAME),Linux)
  ARCH	= -Linux
endif

# AES object files from NIST needed by PRNG for KATs
ifeq ($(TARGET),x64)
  LWEKE_HOME = ../NIST/Additional_Implementations/x64/$(KEM_DIR)
  OBJS       = $(addprefix $(LWEKE_HOME)/objs/,aes/aes_ni.o sha3/fips202.o sha3/fips202x4.o sha3/keccak4x/KeccakP-1600-times4-SIMD256.o) include/x64/aes$(ARCH).o include/x64/Hacl_AesNI.o include/x64/Hacl_AES128.o
  KECCAK     = x64/Hacl_Keccak.c
else ifeq ($(TARGET),)
  LWEKE_HOME ?= ../NIST/Reference_Implementation/reference/$(KEM_DIR)
  OBJS       = $(LWEKE_HOME)/objs/aes/aes_c.o $(LWEKE_HOME)/objs/sha3/fips202.o
  KECCAK     = Hacl_Keccak.c
else
  $(error ERROR: TARGET must be either unset or x64)
endif

CACHE_DIR     = .cache.$(VARIANT)
OUTPUT_DIR    = .output.$(VARIANT)
HINT_DIR      = .hints.$(VARIANT)
GENERATED_DIR = frodo-c.$(VARIANT)
OUT_DIR	      = frodo-c.$(VARIANT)

# CACHE_DIR     .checked    
# OUTPUT_DIR    .krml	      
# HINT_DIR      .hints      
# GENERATED_DIR .c, .h, .d  
# OUT_DIR       .o, .a

.PHONY: test lib stage1 stage2 KATs benchmark clean clean-c distclean

# Manual staging. The default target is test for 64-cSHAKE, lib for the rest 
ifeq ($(VARIANT),64-cSHAKE)
test:
	rm -f .depend && $(MAKE) .depend
	$(MAKE) stage1
	STAGE=2 $(MAKE) stage2

stage2: $(OUT_DIR)/test.exe
	$(OUT_DIR)/test.exe
else
lib:
	rm -f .depend && $(MAKE) .depend
	rm -f $(CACHE_DIR)/Hacl.Impl.Frodo.Params.fst.checked
	$(MAKE) stage1
	STAGE=2 $(MAKE) stage2

stage2: $(OUT_DIR)/libfrodo_for_testing.a $(OUT_DIR)/libfrodo.a

KATs: $(OUT_DIR)/libfrodo_for_testing.a
	make -C $(LWEKE_HOME) USE_OPENSSL=FALSE GENERATION_A=$(GENERATION_A) KATS-fstar
	(cd $(LWEKE_HOME); frodo/PQCtestKAT_kem_fstar)

benchmark: $(OUT_DIR)/libfrodo.a
	make -C $(LWEKE_HOME) USE_OPENSSL=FALSE GENERATION_A=$(GENERATION_A) tests-fstar
	(cd $(LWEKE_HOME); frodo/test_KEM_fstar)
endif # VARIANT = 64-cSHAKE

stage1: $(GENERATED_DIR)/Makefile.include

# 1. Generation of .krml files
# - generate the F* dependency graph via `fstar --dep full`
# - verify each F* file to generate a .checked file
# - extract each .checked file into a .krml file

FSTAR_INCLUDE_DIRS = \
  params-$(VARIANT)$(TARGET) \
  ../spec \
  ../spec/params-$(VARIANT) \
  $(HACL_KREMLIN) \
  $(KREMLIN_HOME)/kremlib \
  $(HACL_HOME)/specs \
  $(HACL_HOME)/lib \
  $(HACL_HOME)/lib/fst \
  $(HACL_HOME)/lib/c \
  $(HACL_HOME)/code/sha3

FSTAR_FLAGS = $(OTHERFLAGS) --cmi \
  --cache_checked_modules --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
  $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_FLAGS)

ENABLE_HINTS = --use_hints --use_hint_hashes --record_hints --query_stats

ROOTS = Hacl.Test.Frodo.fst

.PRECIOUS: %.krml

.depend:
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar +FStar.UInt128 -LowStar -Spec -Frodo.KEM' > $@

include .depend

# Admit SMT queries for modules in FStar, LowStar, C, Lib, and Spec namespaces
$(CACHE_DIR)/FStar.%.checked: | .depend
	$(FSTAR) $< --admit_smt_queries true && \
	touch $@

$(CACHE_DIR)/LowStar.%.checked: | .depend
	$(FSTAR) $< --admit_smt_queries true && \
	touch $@

$(CACHE_DIR)/C.%.checked: | .depend
	$(FSTAR) $< --admit_smt_queries true && \
	touch $@

$(CACHE_DIR)/Lib.%.checked: | .depend
	$(FSTAR) $< --admit_smt_queries true && \
	touch $@

$(CACHE_DIR)/Spec.%.checked: | .depend
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

KREMLIN_TESTLIB = -add-include '"extracted/TestLib.h"' $(KREMLIB)/c/testlib.c

KREMLIN = $(KREMLIN_HOME)/krml

ifeq ($(VARIANT),64-cSHAKE)
ALL_KRML_INPUTS = $(ALL_KRML_FILES)
else
ALL_KRML_INPUTS = $(filter-out $(OUTPUT_DIR)/Hacl_Test_Frodo.krml, $(ALL_KRML_FILES))
endif

# We use -drop (deprecated) only to avoid creating unnecessary .c,.h files
$(GENERATED_DIR)/Makefile.include: $(ALL_KRML_INPUTS) | .depend
	$(KREMLIN) $(KREMLIN_TESTLIB) -skip-compilation \
	-no-prefix 'Hacl.Test.Frodo' \
	-no-prefix 'Hacl.Impl.Matrix' \
	-no-prefix 'Hacl.Impl.Frodo.Params' \
	-no-prefix 'Hacl.Impl.Frodo.Pack' \
	-no-prefix 'Hacl.Impl.Frodo.Encode' \
	-no-prefix 'Hacl.Impl.Frodo.Sample' \
	-no-prefix 'Hacl.Impl.Frodo.Gen' \
	-no-prefix 'Hacl.Impl.Frodo.KEM' \
	-no-prefix 'Hacl.Impl.Frodo.KEM.KeyGen' \
	-no-prefix 'Hacl.Impl.Frodo.KEM.Encaps' \
	-no-prefix 'Hacl.Impl.Frodo.KEM.Decaps' \
	-no-prefix 'Hacl.Frodo.KEM' \
	-no-prefix 'Hacl.Frodo.Random' \
	-no-prefix 'Hacl.Frodo.Clear' \
	-no-prefix 'Hacl.SHA3' \
	-no-prefix 'Hacl.Impl.SHA3' \
	-bundle 'Hacl.Frodo.KEM=Frodo.Params,Hacl.Impl.Frodo.*,Hacl.Impl.Matrix,Hacl.Frodo.*' \
	-bundle 'Lib.*' \
	-bundle 'Spec.*' \
	-bundle 'C=C.Endianness' \
	-bundle 'Hacl.SHA3=Hacl.Impl.SHA3,Hacl.SHA3' \
	-library 'Hacl.AES128,C,FStar' \
	-drop 'LowStar,Spec,Prims,Lib,C.Loops.*,Frodo.KEM' \
	-add-include '"c/Lib_PrintBuffer.h"' \
	-tmpdir $(GENERATED_DIR) \
	$^

# The Makefile is manually staged because GNU Make does not understand
# dependencies between the Makefiles we include, i.e. it won't first generate
# the .depend, parse it, then generate Makefile.include, parse it, then
# generate dependencies among the C files
ifeq ($(STAGE),2)

# The top-level invocation guarantees that stage1 has been run and this file exists
include $(GENERATED_DIR)/Makefile.include

# 3. Collecting all of our source files, and generating corresponding objects

# ALL_C_FILES is generated by KreMLin; since the Makefile is staged via the
# inclusion of Makefile.include, the automated dependency analysis via $(CC) -MM
# also captures the dependencies between these files.
#
# KreMLin sees the fsti's for various modules and creates .h/.c files for them in
# $(GENERATED_DIR). However, we are only interested in the headers, and drop these
# (mostly empty) C files.
ALL_OUR_FILES = $(filter-out C.c FStar.c Hacl_AES128.c Hacl_Keccak.c, $(ALL_C_FILES))
ALL_GENERATED_FILES = $(addprefix $(GENERATED_DIR)/,$(ALL_OUR_FILES))

ALL_SOURCES = \
  $(ALL_GENERATED_FILES) \
  include/rng.c \
  include/random.c \
  include/$(KECCAK) \
  include/clearwords.c \
  $(HACL_HOME)/lib/c/Lib_PrintBuffer.c

ALL_OBJS = $(patsubst %.c,%.o,$(ALL_SOURCES)) \
	$(LWEKE_HOME)/objs/aes/aes.o \
	$(OBJS)

INCLUDE_DIRS = \
  $(KREMLIN_HOME)/include \
  $(KREMLIN_HOME)/kremlib \
  $(LWEKE_HOME)/sha3 \
  $(HACL_HOME)/lib \
  $(HACL_HOME)/code/sha3

# TODO: remove the last line of warning supressions when --cmi is fixed
CFLAGS += -O3 -march=native -mtune=native -funroll-loops
CFLAGS += $(addprefix -I ,$(INCLUDE_DIRS)) -Wall -Wextra -Werror \
  -Wno-parentheses -Wno-unused-parameter -Wno-unused-variable \
  -Wno-incompatible-pointer-types -Wno-int-conversion -Wno-int-to-pointer-cast

# GNU Make manual section 4.14
%.d: %.c
	@set -e; rm -f $@; \
	  $(CC) -MM $(CFLAGS) $< > $@.$$$$; \
	  sed 's,\($(notdir $*)\)\.o[ :]*,$(dir $@)\1.o $@ : ,g' < $@.$$$$ > $@; \
	  rm -f $@.$$$$

-include $(patsubst %.c,%.d,$(ALL_SOURCES))

$(LWEKE_HOME)/%.o:
	make -C $(LWEKE_HOME) USE_OPENSSL=FALSE GENERATION_A=$(GENERATION_A) $*.o

$(OUT_DIR):
	mkdir -p $@

# 4. Collecting all of the object files into static libraries and test executable

$(OUT_DIR)/libfrodo_for_testing.a: $(filter-out include/random.o, $(ALL_OBJS)) $(LWEKE_HOME)/tests/rng.o | $(OUT_DIR)
	$(AR) rcs -S $(OUT_DIR)/libfrodo_for_testing.a $^
	ranlib $(OUT_DIR)/libfrodo_for_testing.a

$(OUT_DIR)/libfrodo.a: $(filter-out include/rng.o, $(ALL_OBJS)) $(LWEKE_HOME)/objs/random/random.o \
 | $(OUT_DIR)
	$(AR) rcs -S $(OUT_DIR)/libfrodo.a $^
	ranlib $(OUT_DIR)/libfrodo.a

$(OUT_DIR)/test.exe: $(filter-out include/random.o, $(ALL_OBJS)) $(LWEKE_HOME)/tests/rng.o | $(OUT_DIR)
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
