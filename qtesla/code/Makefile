FSTAR_HOME   ?= ../../../FStar
KREMLIN_HOME ?= ../../../kremlin
HACL_HOME    ?= ../..

VARIANT      ?= I
PLATFORM     ?= 64

ifeq ($(VARIANT),I)
else ifeq ($(VARIANT),III-size)
else ifeq ($(VARIANT),III-speed)
else ifeq ($(VARIANT),p-I)
else ifeq ($(VARIANT),p-III)
else
  $(error ERROR: VARIANT must be one of I, III-size, III-speed, p-I, p-III)
endif

# PLATFORM only determines the value of RADIX and the definition of (s)digit_t,
# which will affect whether or not 32-bit or 64-bit arithmetic is used. Binaries are
# always built for the native platform, though, so the binaries themselves will always be
# built for that.
ifeq ($(PLATFORM),32)
  PLATFORM_DEFINE=_PLATFORM_32_
else ifeq ($(PLATFORM),64)
  PLATFORM_DEFINE=_PLATFORM_64_
else
  $(error ERROR: PLATFORM must be one of 32, 64)
endif

# REF_HOME=../reference/Reference_implementation/qTesla_$(subst -,_,$(VARIANT))

CACHE_DIR     = .cache.$(VARIANT).$(PLATFORM)
OUTPUT_DIR    = .output.$(VARIANT).$(PLATFORM)
HINT_DIR      = .hints.$(VARIANT).$(PLATFORM)
GENERATED_DIR = qtesla-c.$(VARIANT).$(PLATFORM)
OUT_DIR	      = qtesla-c.$(VARIANT).$(PLATFORM)

# CACHE_DIR     .checked    
# OUTPUT_DIR    .krml	      
# HINT_DIR      .hints      
# GENERATED_DIR .c, .h, .d  
# OUT_DIR       .o, .a

.PHONY: test lib stage1 stage2 KATs benchmark clean clean-c distclean

# Manual staging. The default target is test for I-64, lib for the rest 
lib:
	rm -f .depend && $(MAKE) .depend
	rm -f $(CACHE_DIR)/Hacl.Impl.QTesla.Params.fst.checked
	$(MAKE) stage1
	STAGE=2 $(MAKE) stage2

stage2: $(OUT_DIR)/libqtesla.a $(OUT_DIR)/test-qtesla-$(VARIANT) $(OUT_DIR)/PQCgenKAT_sign-$(VARIANT) $(OUT_DIR)/PQCtestKAT_sign-$(VARIANT)

#KATs: $(OUT_DIR)/libqtesla.a
#	make -C $(REF_HOME) tests-fstar
#	(cd $(REF_HOME); fstar_PQCtestKAT_sign-$(VARIANT))

#benchmark: $(OUT_DIR)/libqtesla.a
#	make -C $(REF_HOME) tests-fstar
#	(cd $(REF_HOME); fstar_test_qtesla-$(VARIANT))

stage1: $(GENERATED_DIR)/Makefile.include

# 1. Generation of .krml files
# - generate the F* dependency graph via `fstar --dep full`
# - verify each F* file to generate a .checked file
# - extract each .checked file into a .krml file

FSTAR_INCLUDE_DIRS = \
  ../spec \
  ../spec/params-$(VARIANT) \
  params-$(VARIANT) \
  platform-$(PLATFORM) \
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

ENABLE_HINTS = --query_stats --use_hints --use_hint_hashes --record_hints # --log_queries

ROOTS = Hacl.Impl.QTesla.fst

.PRECIOUS: %.krml

.depend:
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar +FStar.UInt128 -LowStar -Spec' > $@

include .depend

$(HINT_DIR):
	mkdir -p $@

# Admit SMT queries for modules in FStar, LowStar, C, Lib, and Spec namespaces
$(CACHE_DIR)/FStar.%.checked: | .depend $(HINT_DIR)
	$(FSTAR) $< --admit_smt_queries true && \
	touch $@

$(CACHE_DIR)/LowStar.%.checked: | .depend $(HINT_DIR)
	$(FSTAR) $< --admit_smt_queries true && \
	touch $@

$(CACHE_DIR)/C.%.checked: | .depend $(HINT_DIR)
	$(FSTAR) $< --admit_smt_queries true && \
	touch $@

$(CACHE_DIR)/Lib.%.checked: | .depend $(HINT_DIR)
	$(FSTAR) $< --admit_smt_queries true && \
	touch $@

$(CACHE_DIR)/Spec.%.checked: | .depend $(HINT_DIR)
	$(FSTAR) $< --admit_smt_queries true && \
	touch $@

$(CACHE_DIR)/%.checked: | .depend $(HINT_DIR)
	$(FSTAR) $< $(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(notdir $<).hints && \
	touch $@

$(OUTPUT_DIR)/%.krml: | .depend
	$(FSTAR) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

# 2. Generation of .c files

KREMLIN_TESTLIB = -add-include '"dist/generic/TestLib.h"' $(KREMLIB)/c/testlib.c

KREMLIN = $(KREMLIN_HOME)/krml

ALL_KRML_INPUTS = $(ALL_KRML_FILES)

# We use -drop (deprecated) only to avoid creating unnecessary .c,.h files
$(GENERATED_DIR)/Makefile.include: $(ALL_KRML_INPUTS) | .depend
	$(KREMLIN) $(KREMLIN_TESTLIB) -skip-compilation \
	-no-prefix 'Hacl.Test.QTesla' \
	-no-prefix 'Hacl.Impl.QTesla' \
	-no-prefix 'Hacl.Impl.QTesla.Params' \
        -no-prefix 'Hacl.Impl.QTesla.Pack' \
        -no-prefix 'Hacl.Impl.QTesla.Constants' \
        -no-prefix 'Hacl.Impl.QTesla.Poly' \
        -no-prefix 'Hacl.Impl.QTesla.Heuristic.Pack' \
        -no-prefix 'Hacl.Impl.QTesla.Heuristic.Poly' \
        -no-prefix 'Hacl.Impl.QTesla.Provable.Pack' \
        -no-prefix 'Hacl.Impl.QTesla.Provable.Poly' \
        -no-prefix 'Hacl.Impl.QTesla.Gauss' \
        -no-prefix 'Hacl.Impl.QTesla.Globals' \
	-no-prefix 'Hacl.SHA3' \
	-no-prefix 'Hacl.Impl.SHA3' \
	-bundle 'Hacl.Impl.QTesla=QTesla.Params,Hacl.Impl.QTesla.*' \
	-bundle 'Lib.*' \
	-bundle 'Spec.*' \
	-bundle 'C=C.Endianness' \
	-bundle 'Hacl.SHA3=Hacl.Impl.SHA3,Hacl.SHA3' \
	-library 'C,FStar' \
	-drop 'LowStar,Spec,Prims,Lib' \
	-add-include '"Lib_PrintBuffer.h"' \
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
ALL_OUR_FILES = $(filter-out C.c FStar.c Hacl_Keccak.c, $(ALL_C_FILES))
ALL_GENERATED_FILES = $(addprefix $(GENERATED_DIR)/,$(ALL_OUR_FILES))

ALL_SOURCES = \
  $(ALL_GENERATED_FILES) \
  $(HACL_HOME)/lib/c/Lib_PrintBuffer.c
#  random/random.c \

ALL_OBJS = $(patsubst %.c,%.o,$(ALL_SOURCES)) \
	$(OBJS)

INCLUDE_DIRS = \
  $(KREMLIN_HOME)/include \
  $(KREMLIN_HOME)/kremlib \
  $(HACL_HOME)/dist/hacl-internal-headers \
  $(HACL_HOME)/code/sha3 \
  $(OUT_DIR)

# Definition needed for building reference test code
ARCHITECTURE=_AMD64_
ifeq "$(ARCH)" "x64"
    ARCHITECTURE=_AMD64_
else ifeq "$(ARCH)" "x86"
    ARCHITECTURE=_X86_
else ifeq "$(ARCH)" "ARM"
    ARCHITECTURE=_ARM_
else ifeq "$(ARCH)" "ARM64"
    ARCHITECTURE=_ARM64_
endif

# TODO: remove the last line of warning supressions when --cmi is fixed
CFLAGS += -ggdb -march=native -mtune=native -funroll-loops
CFLAGS += $(addprefix -I ,$(INCLUDE_DIRS)) -Wall -Wextra -Werror \
  -Wno-parentheses -Wno-unused-parameter -Wno-unused-variable \
  -Wno-incompatible-pointer-types -Wno-int-conversion -Wno-int-to-pointer-cast \
  -D $(ARCHITECTURE) -D _qTESLA_$(subst -,_,$(VARIANT))_ -D $(PLATFORM_DEFINE)

# GNU Make manual section 4.14
%.d: %.c
	@set -e; rm -f $@; \
	  $(CC) -MM $(CFLAGS) $< > $@.$$$$; \
	  sed 's,\($(notdir $*)\)\.o[ :]*,$(dir $@)\1.o $@ : ,g' < $@.$$$$ > $@; \
	  rm -f $@.$$$$

-include $(patsubst %.c,%.d,$(ALL_SOURCES))

# Redirect build outputs from test code into the qtesla-c.$(VARIANT).$(PLATFORM) subdirectory. By default they will go
# into the tests-c subdirectory, but then builds for different parameter sets from the same family won't rebuild
# these files properly, and the object code built with another set of parameters will be linked into the test executable,
# which causes all sorts of things to be wrong.
SOURCES_TESTS_C = $(addprefix tests-c/,cpucycles.c random.c rng.c test_qtesla.c PQCgenKAT_sign.c PQCtestKAT_sign.c)
OBJS_TESTS_C = $(subst tests-c/,$(OUT_DIR)/,$(patsubst %.c,%.o,$(SOURCES_TESTS_C)))

OBJS_TEST = $(addprefix $(OUT_DIR)/,cpucycles.o random.o test_qtesla.o)
OBJS_KATS_GEN = $(addprefix $(OUT_DIR)/,rng.o PQCgenKAT_sign.o)
OBJS_KATS_TEST = $(addprefix $(OUT_DIR)/,rng.o PQCtestKAT_sign.o)

ifeq "$(OS)" "Windows_NT"
    OS_DEFINE=__WINDOWS__
    ADDLLIBS=-lbcrypt
else
    OS_DEFINE=__LINUX__
    ADDLLIBS=
endif

$(OBJS_TESTS_C): $(patsubst %.o,%.c,$(subst $(OUT_DIR)/,tests-c/,$@))
	$(CC) -c $(CFLAGS) -D $(OS_DEFINE) -o $@ $(patsubst %.o,%.c,$(subst $(OUT_DIR)/,tests-c/,$@))

#$(REF_HOME)/%.o:
#	make -C $(REF_HOME) $*.o

$(OUT_DIR):
	mkdir -p $@

# 4. Collecting all of the object files into static libraries and test executable

$(OUT_DIR)/libqtesla.a: $(ALL_OBJS) | $(OUT_DIR)
	$(AR) rcs -S $(OUT_DIR)/libqtesla.a $^
	ranlib $(OUT_DIR)/libqtesla.a

$(OUT_DIR)/test-qtesla-$(VARIANT): $(OBJS_TEST) $(OUT_DIR)/libqtesla.a
	$(CC) $(CFLAGS) -o $@ $^ -L $(KREMLIN_HOME)/kremlib/dist/generic -lkremlib $(ADDLLIBS)

$(OUT_DIR)/PQCgenKAT_sign-$(VARIANT): $(OBJS_KATS_GEN) $(OUT_DIR)/libqtesla.a
	$(CC) $(CFLAGS) -o $@ $^ -L $(KREMLIN_HOME)/kremlib/dist/generic -lkremlib -lcrypto

$(OUT_DIR)/PQCtestKAT_sign-$(VARIANT): $(OBJS_KATS_TEST) $(OUT_DIR)/libqtesla.a
	$(CC) $(CFLAGS) -o $@ $^ -L $(KREMLIN_HOME)/kremlib/dist/generic -lkremlib -lcrypto

#$(OUT_DIR)/test.exe: $(ALL_OBJS) $(REF_HOME)/tests/rng.o | $(OUT_DIR)
#	$(info ALL_SOURCES is $(ALL_SOURCES))
#	$(CC) $(CFLAGS) -o $@ $^ -L $(KREMLIN_HOME)/kremlib/dist/generic -lkremlib

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
