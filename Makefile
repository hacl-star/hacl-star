# This Makefile covers all of the present repository (HACL* + Vale + EverCrypt)
# with the exclusion of legacy code found in secure_api, code/old and specs/old.
#
# From a high-level perspective, the coarse-grained dependency graph is:
#
#            merkle_tree
#                |
#             evercrypt
#               /  \
#           code   vale
#           /   \  /
#         lib   specs
#
# This Makefile honors the following variables:
# - NOSHORTLOG=1 disables pretty (short) logs
# - NODEPEND=1 disables .depend re-generation (use for debugging only)
# - SKIPDEPEND=1 disables even *including* .depend files (not meant for end users)
# - NOOPENSSLCHECK=1 disables OpenSSL libcrypto.a checks (useful for verifying files
#   only, or for non-OpenSSL configurations)
# - EVERCRYPT_CONFIG allows switching EverCrypt static configurations; when
#   going through the all target, we properly invalidate the checked file.
#
# This is a staged Makefile, because we first need to generate .fst files out of
# .vaf files in order to get a full dependency graph for the .fst files. So,
# this Makefile exposes the following targets to the end user:
# - all: staged target for the entire build (default)
# - test: staged
# - vale-fst: the minimum needed to compile .vaf files to .fst files
# - vale-verify: properly staged target for re-verifying all the vale files
# - vale-asm: re-generation of the Vale assemblies in dist/vale
# - hacl-verify: staged target for verifying HACL* files
#   curve25519-verify poly1305-verify chacha20-verify spec-verify
#   code-verify: subsets of hacl-verify (each staged)
#
# To generate a Makefile for the interactive mode, use:
# - make foo/bar/Makefile
#
# CI targets:
# - ci: staged, runs all + test, without short logs (this repository's CI)
# - min-test: staged, runs only a subset of verification for the purposes of
#   F*'s extended CI

include Makefile.common

#########################
# Catching setup errors #
#########################

ifeq (3.81,$(MAKE_VERSION))
  $(error You seem to be using the OSX antiquated Make version. Hint: brew \
    install make, then invoke gmake instead of make)
endif

# Better error early.
ifeq (,$(NOVALE))
ifneq (hacl-verify,$(MAKECMDGOALS))

ifeq (,$(wildcard $(VALE_HOME)))
  $(error The directory $$VALE_HOME does not exist$(newline)(VALE_HOME=$(VALE_HOME)).$(newline)Hint: ./tools/get_vale.sh if you don't have Vale, yet)
endif

ifeq (,$(wildcard $(VALE_HOME)/bin/vale.exe))
  $(error $$VALE_HOME/bin/vale.exe does not exist$(newline)(VALE_HOME=$(VALE_HOME)).$(newline)Hint: ./tools/get_vale.sh if you don't have Vale, yet)
endif

ifneq ($(shell cat $(VALE_HOME)/bin/.vale_version | tr -d '\r'),$(shell cat vale/.vale_version | tr -d '\r'))
  $(error this repository wants Vale $(shell cat vale/.vale_version) but in \
    $$VALE_HOME I found $(shell cat $(VALE_HOME)/bin/.vale_version).$(newline)(VALE_HOME=$(VALE_HOME))$(newline)Hint: ./tools/get_vale.sh)
endif

endif
endif

# Backwards-compat, remove
ifneq (,$(MLCRYPTO_HOME))
OPENSSL_HOME 	:= $(MLCRYPTO_HOME)/openssl
endif

ifeq (,$(NOOPENSSLCHECK))
ifeq (,$(OPENSSL_HOME))
  $(error Please define MLCRYPTO_HOME, possibly using cygpath -m on Windows)
endif

ifeq (,$(OPENSSL_HOME)/libcrypto.a)
  $(error $$OPENSSL_HOME/libcrypto.a does not exist (OPENSSL_HOME=$(OPENSSL_HOME)))
endif
endif

ifneq (,$(HACL_HOME))
ifeq (Windows_NT,$(OS))
  HACL_HOME := $(shell cygpath -m $(HACL_HOME))
endif
endif

##########################
# Top-level entry points #
##########################

all:
	tools/blast-staticconfig.sh $(EVERCRYPT_CONFIG)
	$(MAKE) all-staged

all-unstaged: compile-gcc-compatible compile-msvc-compatible compile-gcc64-only \
  compile-evercrypt-external-headers compile-c89-compatible \
  compile-portable-gcc-compatible \
  dist/wasm/package.json dist/merkle-tree/Makefile.basic compile-mitls \
  obj/libhaclml.cmxa compile-election-guard

# Mozilla does not want to run the configure script, so this means that the
# build of Mozilla will break on platforms other than x86-64
ifeq ($(shell uname -m),x86_64)
all-unstaged: compile-mozilla
endif

# Automatic staging.
%-staged: .last_vale_version
	@echo "[STAGE1] Vale to F*"
	$(MAKE) vale-fst
	@echo "[STAGE2] Main target: $*"
	FSTAR_DEPEND_FLAGS="--warn_error +285" $(MAKE) $*-unstaged

.last_vale_version: vale/.vale_version
	@if [[ -f $@ && $$(cat $@) != $$(cat $<) ]]; then \
	  echo ℹ️  Vale tool upgrade detected; \
	  find vale -name '*.vaf' -exec touch {} \; ; \
	fi
	cp $< $@

test: test-staged
test-unstaged: test-handwritten test-c test-ml vale_testInline test-wasm test-bindings-ocaml

# Any file in code/tests is taken to contain an `int main()` function.
# Test should be renamed into Test.EverCrypt
test-c: $(subst .,_,$(patsubst %.fst,test-c-%,$(notdir $(wildcard code/tests/*.fst)))) \
  test-c-Test
	cp dist/Makefile.test dist/test/c/Makefile

# Any file in specs/tests is taken to contain a `val test: unit -> bool` function.
test-ml: $(subst .,_,$(patsubst %.fst,test-ml-%,$(notdir $(wildcard specs/tests/*.fst))))

mozilla-ci: mozilla-ci-staged
mozilla-ci-unstaged: compile-mozilla test-c

# Not reusing the -staged automatic target so as to export NOSHORTLOG
ci:
	NOSHORTLOG=1 $(MAKE) vale-fst
	FSTAR_DEPEND_FLAGS="--warn_error +285" NOSHORTLOG=1 $(MAKE) all-unstaged test-unstaged doc-wasm doc-ocaml
	$(MAKE) -C providers/quic_provider # needs a checkout of miTLS, only valid on CI
	./tools/sloccount.sh

# Not reusing the -staged automatic target so as to export MIN_TEST
min-test:
	MIN_TEST=1 NOSHORTLOG=1 $(MAKE) vale-fst
	MIN_TEST=1 FSTAR_DEPEND_FLAGS="--warn_error +285" NOSHORTLOG=1 \
	  $(MAKE) min-test-unstaged

# So that this Makefile can also clean the previous directory layout. In the
# long run, TO_CLEAN should be able to go.
TO_CLEAN=$(foreach ext,checked checked.lax out cmd err time dump types.vaf krml cmx cmo cmi o d a,-or -iname '*.$(ext)')
clean:
	find . -iname '.depend*' $(TO_CLEAN) -delete
	find obj -maxdepth 1 -mindepth 1 -not -name .gitignore -delete


#################
# Configuration #
#################

IMPORT_FSTAR_TYPES := $(VALE_HOME)/bin/importFStarTypes.exe
PYTHON3 ?= $(shell tools/findpython3.sh)
ifeq ($(OS),Windows_NT)
  MONO =
else
  MONO = mono
endif

ifeq ($(shell uname -s),Darwin)
  ifeq (,$(shell which gsed))
    $(error gsed not found; try brew install gnu-sed)
  endif
  SED := gsed -i
  ifeq (,$(shell which gtime))
    $(error gtime not found; try brew install gnu-time)
  endif
  TIME := gtime -q -f '%E'
else ifeq ($(shell uname -s),FreeBSD)
    SED := sed -i ''
    TIME := /usr/bin/time
else
  SED := sed -i
  TIME := /usr/bin/time -q -f '%E'
endif

ifneq ($(OS),Windows_NT)
ifneq ($(shell realpath $$(pwd)),$(shell realpath $(HACL_HOME)))
  $(error HACL_HOME, currently set to $(HACL_HOME), does not seem to point to the current directory)
endif
endif


##########################
# Pretty-printing helper #
##########################

SHELL:=$(shell which bash)

# A helper to generate pretty logs, callable as:
#   $(call run-with-log,CMD,TXT,STEM)
#
# Arguments:
#  CMD: command to execute (may contain double quotes, but not escaped)
#  TXT: readable text to print out once the command terminates
#  STEM: path stem for the logs, stdout will be in STEM.out, stderr in STEM.err, CMD in STEM.cmd
ifeq (,$(NOSHORTLOG))
run-with-log = \
  @echo "$(subst ",\",$1)" > $3.cmd; \
  $(TIME) -o $3.time sh -c "$(subst ",\",$1)" > $3.out 2> >( tee $3.err 1>&2 ); \
  ret=$$?; \
  time=$$(cat $3.time); \
  if [ $$ret -eq 0 ]; then \
    echo "$2, $$time"; \
  else \
    echo "<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>"; \
    echo -e "\033[31mFatal error while running\033[0m: $1"; \
    echo -e "\033[31mFailed after\033[0m: $$time"; \
    echo -e "\033[36mFull log is in $3.{out,err}, see excerpt below\033[0m:"; \
    tail -n 20 $3.err; \
    echo "<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>"; \
    false; \
  fi
else
run-with-log = $1
endif


####################################################
# Dependency graphs for Vale, then F* source files #
####################################################

# Transforms any foo/bar/baz.qux into obj/baz.qux
to-obj-dir = $(addprefix obj/,$(notdir $1))

# The set of .vaf files we want to translate to F*.
VALE_ROOTS = $(wildcard $(addsuffix /*.vaf,$(VALE_DIRS)))

# Target F* files stemming from Vale files
VAF_AS_FSTS = $(patsubst %.vaf,%.fsti,$(VALE_ROOTS)) $(patsubst %.vaf,%.fst,$(VALE_ROOTS))
VALE_FSTS = $(call to-obj-dir,$(VAF_AS_FSTS))

.PRECIOUS: %.fst %.fsti

# The complete set of F* files, both hand-written and Vale-generated. Note that
# this is only correct in the second stage of the build.
FSTAR_ROOTS = $(wildcard $(addsuffix /*.fsti,$(ALL_HACL_SOURCE_DIRS)) \
    $(addsuffix /*.fst,$(ALL_HACL_SOURCE_DIRS))) \
  $(FSTAR_HOME)/ulib/LowStar.Endianness.fst \
  $(wildcard $(VALE_FSTS)) # empty during the first stage

# We currently force regeneration of three depend files. This is long.

# If were are debugging (i.e. the files exist already); or within a restarting
# (NOT recursive) make invocation, meaning we are in the process of
# re-generating such files; then don't provide recipes for generating .depend
# files. (In the latter case, this would send make into an infinite loop.)

ifndef NODEPEND
ifndef MAKE_RESTARTS
# Note that the --extract 'OCaml:...' argument controls what is extracted for OCaml,
# meaning we can eliminate large chunks of the dependency graph, since we only
# need to run: Vale stuff, and HACL spec tests.
# For KaRaMeL, we use --extract 'krml:*' to extract everything and let krml
# decide what to keep based on reachability and bundling
.fstar-depend-%: .FORCE
	@if ! [ -f .didhelp ]; then echo "💡 Did you know? If your dependency graph didn't change (e.g. no files added or removed, no reference to a new module in your code), run NODEPEND=1 make <your-target> to skip dependency graph regeneration!"; touch .didhelp; fi
	$(call run-with-log,\
	  $(FSTAR_NO_FLAGS) --dep $* $(notdir $(FSTAR_ROOTS)) --warn_error '-285' $(FSTAR_DEPEND_FLAGS) \
	    --extract 'krml:*' \
	    --extract 'OCaml:-* +FStar.Krml.Endianness +Vale.Arch +Vale.X64 -Vale.X64.MemoryAdapters +Vale.Def +Vale.Lib +Vale.Bignum.X64 -Vale.Lib.Tactics +Vale.Math +Vale.Transformers +Vale.AES +Vale.Interop +Vale.Arch.Types +Vale.Arch.BufferFriend +Vale.Lib.X64 +Vale.SHA.X64 +Vale.SHA.SHA_helpers +Vale.Curve25519.X64 +Vale.Poly1305.X64 +Vale.Inline +Vale.AsLowStar +Vale.Test +Spec +Lib -Lib.IntVector -Lib.Memzero0 -Lib.Buffer -Lib.MultiBuffer +C -C.String -C.Failure' > $@ && \
	  $(SED) 's!$(HACL_HOME)/obj/\(.*.checked\)!obj/\1!;s!/bin/../ulib/!/ulib/!g' $@ \
	  ,[FSTAR-DEPEND ($*)],$(call to-obj-dir,$@))

.vale-depend: .fstar-depend-make .FORCE
	$(call run-with-log,\
	  "$(PYTHON3)" tools/valedepend.py \
	    $(addprefix -include ,$(INCLUDES)) \
	    $(addprefix -in ,$(VALE_ROOTS)) \
	    -dep $< \
	    > $@ && \
	  $(SED) 's!$(HACL_HOME)/obj/\(.*.checked\)!obj/\1!g' $@ \
	  ,[VALE-DEPEND],$(call to-obj-dir,$@))

.PHONY: .FORCE
.FORCE:
endif
endif

# If invoking a known, staged target, then don't include these files, so as not
# to trigger their re-generation (will be done later through recursive (NOT
# restarting)) make invocations.
ifeq ($(MAKECMDGOALS),clean)
  SKIPDEPEND=1
else ifeq ($(MAKECMDGOALS),)
  SKIPDEPEND=1
else ifeq ($(MAKECMDGOALS),test)
  SKIPDEPEND=1
else ifeq ($(MAKECMDGOALS),all)
  SKIPDEPEND=1
else ifeq (,$(filter-out %-staged,$(MAKECMDGOALS)))
  SKIPDEPEND=1
else ifeq (,$(filter-out %-verify,$(MAKECMDGOALS)))
  SKIPDEPEND=1
else ifeq ($(MAKECMDGOALS),ci)
  SKIPDEPEND=1
else ifeq ($(MAKECMDGOALS),min-test)
  SKIPDEPEND=1
else ifeq (,$(filter-out %/Makefile,$(MAKECMDGOALS)))
  SKIPDEPEND=1
endif

ifndef SKIPDEPEND
include .fstar-depend-full
include .vale-depend
endif


#################################################
# First stage: compiling vaf files to fst files #
#################################################

%.dump:
	$(call run-with-log,\
	  $(FSTAR) --dump_module $(subst prims,Prims,$(basename $(notdir $*))) \
	    --print_implicits --print_universes --print_effect_args --print_full_names \
	    --print_bound_var_types --ugly --admit_smt_queries true \
	    --hint_file hints/$(notdir $*).hints \
	    $(notdir $*) > $@ \
	  ,[DUMP] $(notdir $(patsubst %.fst,%,$*)),$(call to-obj-dir,$@))

%.types.vaf:
	$(call run-with-log,\
	  $(MONO) $(IMPORT_FSTAR_TYPES) $(addprefix -in ,$^) -out $@ \
	  ,[VALE-TYPES] $(notdir $*),$(call to-obj-dir,$@))

# Always pass Vale.Lib.Operator.vaf as an -include to Vale, except for the file itself.
VALE_FLAGS = -include $(HACL_HOME)/vale/code/lib/util/Vale.Lib.Operator.vaf

obj/Vale.Lib.Operator.fst: VALE_FLAGS=

# Since valedepend generates "foo.fsti: foo.fst", ensure that the fsti is
# more recent than the fst (we don't know in what order vale.exe writes
# the files). (Actually, we know, hence this extra touch.)
%.fst:
	$(call run-with-log,\
	  $(MONO) $(VALE_HOME)/bin/vale.exe -fstarText \
	    -include $*.types.vaf \
	    $(VALE_FLAGS) \
	    -in $< -out $@ -outi $@i && touch -c $@i \
	  ,[VALE] $(notdir $*),$(call to-obj-dir,$@))

# A pseudo-target for the first stage.
vale-fst: $(VALE_FSTS)


################################################
# Verifying F* files to produce .checked files #
################################################

# $(call only-for,<filter>) retains all the checked files that match <filter>,
# taken from the source directories, then returns the corresponding set of
# targets in obj/. For instance, $(call only-for,$(HACL_HOME)/code/%.checked)
# returns obj/Hacl.Hash.Definitions.fst.checked, and all the other targets that
# originate from source files in code/.
#
# With this macro, we no longer rely on pattern rules for file-specific options,
# meaning we also no longer rely on the shortest stem rule. Many of the rules
# below match the same file multiple times (as we the case in the original
# SConstruct). The last match has precedence and overrides previous variable
# assignments.
only-for = $(call to-obj-dir,$(filter $1,$(addsuffix .checked,$(FSTAR_ROOTS) $(VAF_AS_FSTS))))

$(call only-for,$(HACL_HOME)/vale/%.checked): \
  FSTAR_FLAGS=$(VALE_FSTAR_FLAGS)

$(call only-for,$(HACL_HOME)/vale/specs/%.checked): \
  FSTAR_FLAGS=$(VALE_FSTAR_FLAGS)
$(call only-for,$(HACL_HOME)/vale/code/%.checked): \
  FSTAR_FLAGS=$(VALE_FSTAR_FLAGS)

$(addsuffix .checked,$(VALE_FSTS)): \
  FSTAR_FLAGS=$(VALE_FSTAR_FLAGS)

hints:
	mkdir -p $@

# The actual default invocation. Note that the FSTAR_FLAGS= definition allows
# making sure prerequisites of a given rule (e.g. CanonCommMonoid) don't inherit
# the variable assignment of their parent rule.

%.checked: FSTAR_FLAGS=
%.checked: | hints
	$(call run-with-log,\
	  $(FSTAR) $< $(FSTAR_FLAGS) \
	    --hint_file hints/$(notdir $*).hints \
	    && \
	    touch -c $@ \
	  ,[VERIFY] $(notdir $*),$(call to-obj-dir,$@))

%-verify: %-verify-staged
	@

vale-verify-unstaged: \
  $(addsuffix .checked,$(VALE_FSTS)) \
  $(call only-for,$(HACL_HOME)/vale/%.checked) \

# Overriding the pattern rule and making this one unstaged.
code-verify-unstaged: $(call only-for,$(HACL_HOME)/code/%)
spec-verify-unstaged: $(call only-for,$(HACL_HOME)/specs/%)
lib-verify-unstaged: $(call only-for,$(HACL_HOME)/lib/%)
curve25519-verify-unstaged: $(call only-for,$(HACL_HOME)/code/curve25519/%)
poly1305-verify-unstaged: $(call only-for,$(HACL_HOME)/code/poly1305/%)
chacha20-verify-unstaged: $(call only-for,$(HACL_HOME)/code/chacha20/%)
salsa20-verify-unstaged: $(call only-for,$(HACL_HOME)/code/salsa20/%)

verify-hacl: code-verify-unstaged spec-verify-unstaged lib-verify-unstaged

############
# min-test #
############

min-test-unstaged: $(filter-out \
  obj/X64.Vale.InsSha.% \
  $(call only-for,$(HACL_HOME)/vale/code/arch/x64/interop/%)\
  ,\
  $(call only-for, $(addprefix $(HACL_HOME)/vale/,\
  code/arch/% code/lib/% code/crypto/poly1305/% \
  code/thirdPartyPorts/OpenSSL/poly1305/% specs/%))) \
  obj/Hacl.Hash.MD.fst.checked
	@echo "<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>"
	@echo MIN_TEST summary: verified the following modules
	@echo $^
	@echo "<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>"

####################################################
# Tactic (not covered by --extract, intentionally) #
####################################################

obj/Meta_Interface.ml: CODEGEN = Plugin
obj/Meta_Interface.ml: obj/Meta.Interface.fst.checked

obj/Meta_Interface.cmxs: obj/Meta_Interface.ml
	$(OCAMLSHARED) $< -o $@

# IMPORTANT NOTE: we cannot let F* compile the cmxs for several reasons.
# First, it won't detect out-of-date .ml files and won't recompile the cmxs.
# Second, it will race because several Hacl.Meta.%.checked targets might be
# scheduled in parallel.
# So, we don't trust F* to compile the tactic and add it as a step of the
# dependency graph. Note that local Makefiles don't bother.
obj/Hacl.Meta.%.checked: FSTAR_FLAGS += --load Meta.Interface
$(filter obj/Hacl.Meta.%.checked,$(call to-obj-dir,$(ALL_CHECKED_FILES))): obj/Meta_Interface.cmxs

###############################################################################
# Extracting (checked files) to OCaml, producing executables, running them to #
# print ASM files                                                             #
###############################################################################

.PRECIOUS: obj/%.cmx
obj/%.cmx: obj/%.ml
	$(call run-with-log,\
	  $(OCAMLOPT) -c $< -o $@ \
	  ,[OCAMLOPT-CMX] $(notdir $*),$(call to-obj-dir,$@))

obj/%.ml: CODEGEN=OCaml

obj/%.ml:
	$(call run-with-log,\
	  $(FSTAR) $(notdir $(subst .checked,,$<)) --codegen $(CODEGEN) \
	    --extract_module $(subst .fst.checked,,$(notdir $<)) \
	  ,[EXTRACT-ML] $(notdir $*),$(call to-obj-dir,$@))

dist/vale:
	mkdir -p $@

dist/vale/%-x86_64-mingw.S: obj/vale-%.exe | dist/vale
	$< GCC Win > $@

dist/vale/%-x86_64-msvc.asm: obj/vale-%.exe | dist/vale
	$< MASM Win > $@

dist/vale/%-x86_64-linux.S: obj/vale-%.exe | dist/vale
	$< GCC Linux > $@

dist/vale/%-x86_64-darwin.S: obj/vale-%.exe | dist/vale
	$< GCC MacOS > $@

dist/vale/%-inline.h: obj/inline-vale-%.exe | dist/vale
	$< > $@

obj/vale-cpuid.exe: vale/code/lib/util/x64/CpuidMain.ml
obj/vale-aesgcm.exe: vale/code/crypto/aes/x64/Main.ml
obj/vale-sha256.exe: vale/code/crypto/sha/ShaMain.ml
obj/vale-curve25519.exe: vale/code/crypto/ecc/curve25519/Main25519.ml
obj/vale-poly1305.exe: vale/code/crypto/poly1305/x64/PolyMain.ml

obj/inline-vale-curve25519.exe: vale/code/crypto/ecc/curve25519/Inline25519.ml
obj/inline-vale-testInline.exe: vale/code/test/TestInlineMain.ml

obj/vale_testInline.h: obj/inline-vale-testInline.exe
	$< > $@

obj/CmdLineParser.ml: vale/code/lib/util/CmdLineParser.ml
	cp $< $@

obj/CmdLineParser.cmx: $(ALL_CMX_FILES)

obj/inline-vale-%.exe: $(ALL_CMX_FILES)
	$(call run-with-log,\
	  $(OCAMLOPT) $^ -o $@ \
	  ,[OCAMLOPT-EXE] $(notdir $*),$@)

obj/vale-%.exe: $(ALL_CMX_FILES) obj/CmdLineParser.cmx
	$(call run-with-log,\
	  $(OCAMLOPT) $^ -o $@ \
	  ,[OCAMLOPT-EXE] $(notdir $*),$@)

# The ones in secure_api are legacy and should go.
VALE_ASMS = $(foreach P,cpuid aesgcm sha256 curve25519 poly1305,\
  $(addprefix dist/vale/,$P-x86_64-mingw.S $P-x86_64-msvc.asm $P-x86_64-linux.S $P-x86_64-darwin.S)) \
  $(wildcard \
    $(HACL_HOME)/secure_api/vale/asm/oldaesgcm-*.S \
    $(HACL_HOME)/secure_api/vale/asm/oldaesgcm-*.asm \
    $(HACL_HOME)/secure_api/vale/asm/aes-*.S \
    $(HACL_HOME)/secure_api/vale/asm/aes-*.asm) \
  dist/vale/curve25519-inline.h

# A pseudo-target for generating just Vale assemblies
vale-asm: $(VALE_ASMS)


###########################################################################
# Extracting (checked files) to krml, then running karamel to generate C. #
###########################################################################

.PRECIOUS: %.krml

obj/%.krml:
	$(call run-with-log,\
	  $(FSTAR) --codegen krml \
	    --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	    $(notdir $(subst .checked,,$<)) && \
	  touch $@ \
	  ,[EXTRACT-KRML] $*,$@)

# For the time being, we rely on the old extraction to give us self-contained
# files for algorithms that haven't been rewritten for HACLv2.

.PHONY: old-%
old-%:
	$(call run-with-log,\
	  KOPTS=-verbose $(MAKE) -C code/old -f Makefile.old $* \
	  ,[OLD-MAKE $*],obj/old-$*)


########################################
# Distributions of EverCrypt and HACL* #
########################################

# A series of definitions that both collect the files that go into a
# distribution, and control the shape of the generated code. All of these
# variables (except for REQUIRED_FLAGS) are intended to be overridden with
# target-specific values (see GNU Make Manual 6.11 "Target-specific Variable Values").

HAND_WRITTEN_C		= Lib.PrintBuffer Lib.RandomBuffer.System

# Always copied into the destination directory, always passed to karamel.
HAND_WRITTEN_FILES 	= $(wildcard $(LIB_DIR)/c/*.c) \
  $(addprefix providers/evercrypt/c/evercrypt_,vale_stubs.c)

# Always copied into the destination directory, not passed to karamel.
HAND_WRITTEN_H_FILES	= $(filter-out $(LIB_DIR)/c/libintvector_debug.h, \
				$(wildcard $(LIB_DIR)/c/*.h))

# OCaml bindings for hand written C files (i.e., not generated by KaRaMeL)
# Non-empty for distributions which have OCaml bindings
HAND_WRITTEN_ML_BINDINGS =
HAND_WRITTEN_ML_GEN =

# Flags that we always include. These are not meant to be overridden and
# provide: -library (for vale interop); -no-prefix (for correct vale interop
# names; for correct Merkle Tree function names used by C tests); -bundle (to
# eliminate spec files where definitions are not marked noextract); -drop (for
# intrinsics, see note below); -add-include (for curve's inline header); -fX for
# codegen customiations; -static-header (so that instead of extern declarations
# we get static inline declarations for inlined Vale routines); and a few other
# tweaks.
#
# Note: I am using the deprecated -drop option, but it's ok because the dropped
# module ends up in another bundle. Maybe the semantics of -drop should be
# changed to just drop the declarations from a given module and then rely on
# karamel's empty-module removal.
#
# When extracting our libraries, we purposely don't distribute tests
#
# See Makefile.include for the definition of VALE_BUNDLES
REQUIRED_BUNDLES = \
  -bundle Hacl.Poly1305.Field32xN.Lemmas[rename=Hacl_Lemmas] \
  -bundle EverCrypt.BCrypt \
  -bundle EverCrypt.OpenSSL \
  -bundle MerkleTree.Spec,MerkleTree.Spec.*,MerkleTree.New.High,MerkleTree.New.High.* \
  $(VALE_BUNDLES) \
  -bundle Hacl.Impl.Poly1305.Fields \
  -bundle 'EverCrypt.Spec.*'

REQUIRED_DROP = \
  -drop EverCrypt.TargetConfig

REQUIRED_FLAGS	= \
  $(REQUIRED_BUNDLES) \
  $(REQUIRED_DROP) \
  -library 'Vale.Stdcalls.*' \
  -no-prefix 'Vale.Stdcalls.*' \
  -static-header 'Vale.Inline.*' \
  -library 'Vale.Inline.X64.Fadd_inline' \
  -library 'Vale.Inline.X64.Fmul_inline' \
  -library 'Vale.Inline.X64.Fswap_inline' \
  -library 'Vale.Inline.X64.Fsqr_inline' \
  -no-prefix 'Vale.Inline.X64.Fadd_inline' \
  -no-prefix 'Vale.Inline.X64.Fmul_inline' \
  -no-prefix 'Vale.Inline.X64.Fswap_inline' \
  -no-prefix 'Vale.Inline.X64.Fsqr_inline' \
  -no-prefix 'EverCrypt.Vale' \
  -add-include 'Hacl_Curve25519_64.c:"curve25519-inline.h"' \
  -no-prefix 'MerkleTree' \
  -no-prefix 'MerkleTree.EverCrypt' \
  -library EverCrypt.AutoConfig,EverCrypt.OpenSSL,EverCrypt.BCrypt \
  -static-header 'EverCrypt.TargetConfig' \
  -no-prefix 'EverCrypt.TargetConfig' \
  $(BASE_FLAGS)

# Disabled for Mozilla (carefully avoiding any KRML_CHECK_SIZE)
TARGET_H_INCLUDE = -add-early-include '"krml/internal/target.h"'

# Note: we include libintvector.h in C files whenever possible, but fall back to
# including this header in .h when the public API of a given algorithm (e.g.
# Poly1305/256) directly refers to a LibIntVector type.
# Note: due to backwards-compat, the syntax for the option is not super great...
# it's `-add-include 'Foo:"bar.h"'` (include added to Foo.h) and
# `-add-include 'Foo.c:"bar.h"'` (include added to Foo.c). Note how the former
# doesn't have the extension while the latter does.
INTRINSIC_FLAGS = \
  -add-include 'Hacl_P256.c:"lib_intrinsics.h"' \
  \
  -add-include 'Hacl_Chacha20Poly1305_128.c:"libintvector.h"' \
  -add-include 'Hacl_Chacha20_Vec128.c:"libintvector.h"' \
  -add-include 'Hacl_SHA2_Vec128.c:"libintvector.h"' \
  \
  -add-include 'Hacl_Hash_Blake2s_128:"libintvector.h"' \
  -add-include 'Hacl_Poly1305_128:"libintvector.h"' \
  \
  -add-include 'Hacl_Chacha20Poly1305_256.c:"libintvector.h"' \
  -add-include 'Hacl_Chacha20_Vec256.c:"libintvector.h"' \
  -add-include 'Hacl_SHA2_Vec256.c:"libintvector.h"' \
  \
  -add-include 'Hacl_Hash_Blake2b_256:"libintvector.h"' \
  -add-include 'Hacl_Poly1305_256:"libintvector.h"' \

# Disabled for distributions that don't include code based on intrinsics.
INTRINSIC_INT_FLAGS = \
  -add-include 'Hacl_P256:"lib_intrinsics.h"' \
  -add-include 'Hacl_Bignum:"lib_intrinsics.h"' \
  -add-include 'Hacl_K256_ECDSA:"lib_intrinsics.h"'

# Disables tests; overriden in Wasm where tests indicate what can be compiled.
TEST_FLAGS = -bundle Test,Test.*,Hacl.Test.*
# Ensures that Lib_RandomBuffer_System.h and Lib_PrintBuffer.h have a constant name
# (and are not subject to bundling). Erased by distributions that don't need
# those files.
HAND_WRITTEN_LIB_FLAGS = -bundle Lib.RandomBuffer.System= -bundle Lib.PrintBuffer= -bundle Lib.Memzero0=
# Disabling by pure-HACL distributions
TARGETCONFIG_FLAGS = -add-include '"evercrypt_targetconfig.h"'

# By default, we strive to do one file per algorithm for HACL, and one file for
# logical unit for EverCrypt (e.g. E_HASH_BUNDLE).
#
# All of these bundles that have something on the left-hand side. They demand
# that a particular feature be enabled. For a distribution to disable the
# corresponding feature, one of these variables needs to be overridden.
E_HASH_BUNDLE=-bundle EverCrypt.Hash+EverCrypt.Hash.Incremental=[rename=EverCrypt_Hash]
MERKLE_BUNDLE=-bundle 'MerkleTree+MerkleTree.EverCrypt+MerkleTree.Low+MerkleTree.Low.Serialization+MerkleTree.Low.Hashfunctions=MerkleTree.*[rename=MerkleTree]'
CTR_BUNDLE=-bundle EverCrypt.CTR=EverCrypt.CTR.*
WASMSUPPORT_BUNDLE = -bundle WasmSupport
LEGACY_BUNDLE = -bundle EverCrypt[rename=EverCrypt_Legacy]

BUNDLE_FLAGS	=\
  $(BLAKE2_BUNDLE) \
  $(HASH_BUNDLE) \
  $(E_HASH_BUNDLE) \
  $(SHA3_BUNDLE) \
  $(SHA2MB_BUNDLE) \
  $(CHACHA20_BUNDLE) \
  $(SALSA20_BUNDLE) \
  $(BIGNUM_BUNDLE) \
  $(CURVE_BUNDLE) \
  $(CHACHAPOLY_BUNDLE) \
  $(ED_BUNDLE) \
  $(POLY_BUNDLE) \
  $(NACLBOX_BUNDLE) \
  $(MERKLE_BUNDLE) \
  $(WASMSUPPORT_BUNDLE) \
  $(CTR_BUNDLE) \
  $(P256_BUNDLE) \
  $(K256_BUNDLE) \
  $(FRODO_BUNDLE) \
  $(HPKE_BUNDLE) \
  $(STREAMING_BUNDLE) \
  $(INTTYPES_BUNDLE) \
  $(INTTYPES_128_BUNDLE) \
  $(RSAPSS_BUNDLE) \
  $(FFDHE_BUNDLE) \
  $(LEGACY_BUNDLE)

DEFAULT_FLAGS = \
  $(HAND_WRITTEN_LIB_FLAGS) \
  $(TARGETCONFIG_FLAGS) \
  $(TEST_FLAGS) \
  $(INTRINSIC_INT_FLAGS) \
  $(INTRINSIC_FLAGS) \
  $(BUNDLE_FLAGS) \
  $(REQUIRED_FLAGS) \
  $(TARGET_H_INCLUDE)

# WASM distribution
# -----------------
#
# We disable anything that is not pure Low*; no intrinsics; no EverCrypt

# TODO: the way externals are handled in Wasm is nuts and they should be in a
# single module rather than require clients to do their surgical bundling.
WASM_STANDALONE=Prims LowStar.Endianness C.Endianness C.String TestLib

WASM_FLAGS	=\
  $(patsubst %,-bundle %,$(WASM_STANDALONE)) \
  -bundle FStar.* \
  -bundle LowStar.* \
  -bundle Lib.RandomBuffer.System \
  -bundle Lib.Memzero \
  -minimal -wasm -d wasm

dist/wasm/Makefile.basic: VALE_ASMS =
dist/wasm/Makefile.basic: HAND_WRITTEN_OPTIONAL_FILES =
dist/wasm/Makefile.basic: HAND_WRITTEN_H_FILES =
dist/wasm/Makefile.basic: HAND_WRITTEN_FILES =
dist/wasm/Makefile.basic: TARGETCONFIG_FLAGS =
dist/wasm/Makefile.basic: INTRINSIC_FLAGS =

# Must appear early on because of the left-to-right semantics of -bundle flags.
dist/wasm/Makefile.basic: HAND_WRITTEN_LIB_FLAGS = $(WASM_FLAGS)

# Doesn't work in WASM because one function has some heap allocation
dist/wasm/Makefile.basic: HASH_BUNDLE += -bundle Hacl.HMAC_DRBG

# Doesn't work in WASM because un-materialized externals for AES128
dist/wasm/Makefile.basic: FRODO_BUNDLE = -bundle Hacl.Frodo.KEM,Hacl.Impl.Frodo.*,Hacl.Impl.Matrix,Hacl.Frodo.*,Hacl.Keccak,Hacl.AES128,Hacl.Frodo64,Hacl.Frodo640,Hacl.Frodo976,Hacl.Frodo1344

dist/wasm/Makefile.basic: INTTYPES_128_BUNDLE = -bundle Hacl.IntTypes.Intrinsics_128

# No Vale Curve64 no "Local" or "Slow" Curve64, only Curve51 (local Makefile hack)
dist/wasm/Makefile.basic: CURVE_BUNDLE_SLOW =
dist/wasm/Makefile.basic: CURVE_BUNDLE = \
  $(CURVE_BUNDLE_BASE) \
  -bundle 'Hacl.Curve25519_64_Slow' \
  -bundle 'Hacl.Curve25519_64' \
  -bundle 'Hacl.Curve25519_64_Local'

# Most HPKE variants don't work in Wasm, since they are either using Curve64,
# P256 or vectorized chacha-poly, none of which are available in Wasm.
dist/wasm/Makefile.basic: HPKE_BUNDLE += \
  -bundle Hacl.HPKE.Curve51_CP32_SHA256= \
  -bundle Hacl.HPKE.Curve51_CP32_SHA512= \
  -bundle 'Hacl.HPKE.*'

# Disabling vectorized stuff
dist/wasm/Makefile.basic: CHACHA20_BUNDLE += \
  -bundle Hacl.Chacha20_Vec128,Hacl.Chacha20_Vec256
dist/wasm/Makefile.basic: CHACHAPOLY_BUNDLE += \
  -bundle Hacl.Chacha20Poly1305_128,Hacl.Chacha20Poly1305_256
dist/wasm/Makefile.basic: POLY_BUNDLE = \
  -bundle 'Hacl.Poly1305_32=Hacl.Impl.Poly1305.Field32xN_32' \
  -bundle 'Hacl.Poly1305_128,Hacl.Poly1305_256,Hacl.Impl.Poly1305.*' \
  -bundle 'Hacl.Streaming.Poly1305_128,Hacl.Streaming.Poly1305_256'
dist/wasm/Makefile.basic: SHA2MB_BUNDLE = -bundle Hacl.Impl.SHA2.*,Hacl.SHA2.Scalar32,Hacl.SHA2.Vec128,Hacl.SHA2.Vec256
dist/wasm/Makefile.basic: BLAKE2_BUNDLE = $(BLAKE2_BUNDLE_BASE) \
  -bundle 'Hacl.Hash.Blake2s_128,Hacl.Blake2s_128,Hacl.Hash.Blake2b_256,Hacl.Blake2b_256' \
  -bundle 'Hacl.HMAC.Blake2s_128,Hacl.HMAC.Blake2b_256,Hacl.HKDF.Blake2s_128,Hacl.HKDF.Blake2b_256' \
  -bundle 'Hacl.Streaming.Blake2s_128,Hacl.Streaming.Blake2b_256'

dist/wasm/Makefile.basic: STREAMING_BUNDLE = -bundle Hacl.Streaming.*

# And Merkle trees
dist/wasm/Makefile.basic: MERKLE_BUNDLE = -bundle 'MerkleTree,MerkleTree.*'
dist/wasm/Makefile.basic: CTR_BUNDLE =
dist/wasm/Makefile.basic: K256_BUNDLE = -bundle Hacl.K256.ECDSA,Hacl.Impl.K256.*,Hacl.K256.*,Hacl.EC.K256
dist/wasm/Makefile.basic: RSAPSS_BUNDLE = -bundle Hacl.RSAPSS,Hacl.Impl.RSAPSS.*,Hacl.Impl.RSAPSS
dist/wasm/Makefile.basic: FFDHE_BUNDLE = -bundle Hacl.FFDHE,Hacl.Impl.FFDHE.*,Hacl.Impl.FFDHE
dist/wasm/Makefile.basic: DEFAULT_FLAGS += -bundle EverCrypt.TargetConfig \
  -bundle 'EverCrypt,EverCrypt.*'
dist/wasm/Makefile.basic: REQUIRED_DROP =

dist/wasm/package.json: dist/wasm/Makefile.basic $(wildcard bindings/js/*.js) bindings/js/README.md $(wildcard bindings/js/*.json) bindings/js/.npmignore
	cp -f $(filter-out %.basic,$^) $(dir $@)
	rm -f $(dir $@)README $(dir $@)main.html $(dir $@)main.js $(dir $@)browser.js $(dir $@)*.wast

dist/wasm/doc/readable_api.js: dist/wasm/package.json
	cd dist/wasm && \
	  mkdir -p doc && \
	  node api_doc.js

dist/wasm/doc/out/index.html: dist/wasm/doc/readable_api.js
	jsdoc $< -d $(dir $@)

ifeq ($(OS),Windows_NT)
doc-wasm:
	echo "WASM documentation disabled (jsdoc segfaults on Windows)"
else
doc-wasm: dist/wasm/doc/out/index.html
endif

publish-test-wasm: dist/wasm/package.json
	cd dist/wasm && \
	  npm publish --dry-run

test-wasm: dist/wasm/package.json
	cd dist/wasm && \
	  node api_test.js && \
	  node test2.js

# Compact distributions
# ---------------------
#
# Our default, flagship distribution with everything. Some slightly different
# variants depending on whether we are compatible with x86, or MSVC, etc. (see
# README.EverCrypt.md)

# Customizations for regular, msvc and gcc flavors.
dist/gcc-compatible/Makefile.basic: DEFAULT_FLAGS += \
  -ctypes EverCrypt.*,Hacl.*
dist/gcc-compatible/Makefile.basic: HAND_WRITTEN_ML_BINDINGS += \
  $(wildcard lib/ml/*_bindings.ml)
dist/gcc-compatible/Makefile.basic: HAND_WRITTEN_ML_GEN += \
  $(wildcard lib/ml/*_gen.ml)
dist/gcc-compatible/Makefile.basic: HAND_WRITTEN_OPTIONAL_FILES += \
  dist/META dist/hacl-star-raw.opam dist/configure

test-bindings-ocaml: compile-gcc-compatible
	if ocamlfind query hacl-star-raw ; then \
	    echo 'WARNING: OCaml package hacl-star-raw already installed' ; \
	else \
	    cd dist/gcc-compatible && make install-hacl-star-raw ; \
	fi
	cd bindings/ocaml && $(LD_EXTRA) dune runtest

doc-ocaml: test-bindings-ocaml
	cd bindings/ocaml && $(LD_EXTRA) dune build @doc

dist/msvc-compatible/Makefile.basic: DEFAULT_FLAGS += -falloca -ftail-calls

dist/gcc64-only/Makefile.basic: DEFAULT_FLAGS += -fbuiltin-uint128

# miTLS
# -----
dist/mitls/Makefile.basic: DEFAULT_FLAGS += -falloca -ftail-calls
dist/mitls/Makefile.basic: LEGACY_BUNDLE =
# This is a broken AES... used by the (awful) EverCrypt.fst which in turns calls
# EverCrypt.HACL.fsti which in turns calls (via C #ifdefs) Crypto.Symmetric.AES
dist/mitls/Makefile.basic: HACL_OLD_FILES = \
  code/old/experimental/aesgcm/aesgcm-c/Hacl_AES.c


# Not passed to karamel, meaning that they don't end up in the Makefile.basic
# list of C source files. They're added manually in dist/Makefile (see ifneq
# tests).
dist/mitls/Makefile.basic: HAND_WRITTEN_OPTIONAL_FILES = \
  $(addprefix providers/evercrypt/c/evercrypt_,openssl.c bcrypt.c)


# C89 distribution
# ----------------
#
# - MerkleTree doesn't compile in C89 mode (FIXME?)
# - Use C89 versions of ancient HACL code
dist/c89-compatible/Makefile.basic: MERKLE_BUNDLE = -bundle 'MerkleTree.*,MerkleTree'
dist/c89-compatible/Makefile.basic: DEFAULT_FLAGS += -fc89 -ccopt -std=c89 -ccopt -Wno-typedef-redefinition


# Election Guard distribution
# ---------------------------
#
# Trying something new, i.e. only listing the things we care about (since
# there's so few of them)
dist/election-guard/Makefile.basic: BUNDLE_FLAGS = \
  -bundle Hacl.Hash.* \
  -bundle Hacl.HMAC \
  -bundle Hacl.Streaming.SHA2= \
  -bundle Hacl.Bignum256= \
  -bundle Hacl.Bignum4096= \
  -bundle Hacl.Bignum256_32= \
  -bundle Hacl.Bignum4096_32= \
  -bundle Hacl.Bignum,Hacl.Bignum.*[rename=Hacl_Bignum] \
  -bundle Hacl.HMAC_DRBG= \
  $(INTTYPES_BUNDLE)
dist/election-guard/Makefile.basic: INTRINSIC_FLAGS =
dist/election-guard/Makefile.basic: VALE_ASMS =
dist/election-guard/Makefile.basic: HAND_WRITTEN_OPTIONAL_FILES =
dist/election-guard/Makefile.basic: HAND_WRITTEN_FILES := $(filter-out %/evercrypt_vale_stubs.c %/Lib_PrintBuffer.c,$(HAND_WRITTEN_FILES))
dist/election-guard/Makefile.basic: HAND_WRITTEN_LIB_FLAGS = -bundle Lib.RandomBuffer.System= -bundle Lib.Memzero0=
dist/election-guard/Makefile.basic: DEFAULT_FLAGS += \
  -bundle '\*[rename=Should_not_be_here]' \
  -falloca -ftail-calls -fc89 -add-early-include '"krml/internal/builtin.h"'

# Mozilla distribution
# --------------------
#
# Disable the EverCrypt and MerkleTree layers. Only keep Chacha20, Poly1305,
# Curve25519 for now. Everything else in Hacl is disabled.
dist/mozilla/Makefile.basic: CURVE_BUNDLE_SLOW = -bundle Hacl.Curve25519_64_Slow
dist/mozilla/Makefile.basic: SALSA20_BUNDLE = -bundle Hacl.Salsa20
dist/mozilla/Makefile.basic: ED_BUNDLE = -bundle Hacl.Ed25519,Hacl.EC.Ed25519
dist/mozilla/Makefile.basic: NACLBOX_BUNDLE = -bundle Hacl.NaCl
dist/mozilla/Makefile.basic: E_HASH_BUNDLE =
dist/mozilla/Makefile.basic: MERKLE_BUNDLE = -bundle MerkleTree.*,MerkleTree
dist/mozilla/Makefile.basic: CTR_BUNDLE =
dist/mozilla/Makefile.basic: BLAKE2_BUNDLE = -bundle Hacl.Impl.Blake2.*,Hacl.Blake2b_256,Hacl.Blake2s_128,Hacl.Blake2b_32,Hacl.Streaming.Blake2s_128,Hacl.Streaming.Blake2b_256,Hacl.Blake2s_32,Hacl.HMAC.Blake2b_256,Hacl.HMAC.Blake2s_128,Hacl.HKDF.Blake2b_256,Hacl.HKDF.Blake2s_128
dist/mozilla/Makefile.basic: SHA2MB_BUNDLE = -bundle Hacl.Impl.SHA2.*,Hacl.SHA2_Vec256,Hacl.SHA2_Vec128,Hacl.SHA2_Scalar32
dist/mozilla/Makefile.basic: HASH_BUNDLE = -bundle Hacl.Hash.*,Hacl.HKDF,Hacl.HMAC,Hacl.HMAC_DRBG
dist/mozilla/Makefile.basic: HPKE_BUNDLE = -bundle 'Hacl.HPKE.*'
dist/mozilla/Makefile.basic: P256_BUNDLE= -bundle Hacl.P256,Hacl.Impl.ECDSA.*,Hacl.Impl.SolinasReduction,Hacl.Impl.P256.*
dist/mozilla/Makefile.basic: K256_BUNDLE= -bundle Hacl.K256.ECDSA,Hacl.Impl.K256.*,Hacl.K256.*,Hacl.EC.K256
dist/mozilla/Makefile.basic: RSAPSS_BUNDLE = -bundle Hacl.Impl.RSAPSS.*,Hacl.Impl.RSAPSS,Hacl.RSAPSS
dist/mozilla/Makefile.basic: FFDHE_BUNDLE = -bundle Hacl.Impl.FFDHE.*,Hacl.Impl.FFDHE,Hacl.FFDHE
dist/mozilla/Makefile.basic: BIGNUM_BUNDLE = -bundle Hacl.Bignum256_32,Hacl.Bignum4096_32,Hacl.Bignum256,Hacl.Bignum4096,Hacl.Bignum32,Hacl.Bignum64,Hacl.GenericField32,Hacl.GenericField64,Hacl.Bignum.*,Hacl.Bignum
dist/mozilla/Makefile.basic: STREAMING_BUNDLE = -bundle Hacl.Streaming.*
dist/mozilla/Makefile.basic: FRODO_BUNDLE = -bundle Hacl.Impl.Frodo.*,Hacl.Frodo.*,Hacl.Keccak,Hacl.Frodo64,Hacl.Frodo640,Hacl.Frodo976,Hacl.Frodo1344
dist/mozilla/Makefile.basic: \
  BUNDLE_FLAGS += \
    -bundle EverCrypt.* \
    -bundle Hacl.Impl.*,Hacl.Bignum25519.*,Hacl.Bignum25519 \
    -bundle Hacl.Chacha20.Vec32
dist/mozilla/Makefile.basic: VALE_ASMS := $(filter dist/vale/curve25519-%,$(VALE_ASMS))
dist/mozilla/Makefile.basic: HAND_WRITTEN_OPTIONAL_FILES =
dist/mozilla/Makefile.basic: HAND_WRITTEN_H_FILES := $(filter %/libintvector.h,$(HAND_WRITTEN_H_FILES))
dist/mozilla/Makefile.basic: HAND_WRITTEN_FILES =
dist/mozilla/Makefile.basic: TARGETCONFIG_FLAGS =
dist/mozilla/Makefile.basic: HAND_WRITTEN_LIB_FLAGS =
dist/mozilla/Makefile.basic: TARGET_H_INCLUDE = -add-early-include '<stdbool.h>'

# Portable distribution
# ---------------------
#
# Binary objects not optimized for the host (possibly CI) machine, meaning that
# someone can download them onto their machine for debugging. Also enforces that
# we don't have bundle errors where, say, an sse2-required function ends up in a
# file that is *NOT* known to require sse2.
dist/portable-gcc-compatible/Makefile.basic: DEFAULT_FLAGS += -rst-snippets

# Merkle Tree standalone distribution
# -----------------------------------
#
# Without even cryptography.
dist/merkle-tree/Makefile.basic: \
	BUNDLE_FLAGS=-bundle MerkleTree.EverCrypt \
    -bundle 'MerkleTree+MerkleTree.Low+MerkleTree.Low.Serialization+MerkleTree.Low.Hashfunctions=*[rename=MerkleTree]'
dist/merkle-tree/Makefile.basic: VALE_ASMS =
dist/merkle-tree/Makefile.basic: HAND_WRITTEN_OPTIONAL_FILES =
dist/merkle-tree/Makefile.basic: HAND_WRITTEN_H_FILES =
dist/merkle-tree/Makefile.basic: HAND_WRITTEN_FILES =
dist/merkle-tree/Makefile.basic: TARGETCONFIG_FLAGS =
dist/merkle-tree/Makefile.basic: HAND_WRITTEN_LIB_FLAGS =
dist/merkle-tree/Makefile.basic: INTRINSIC_FLAGS =

# EVERCRYPT_CONFIG tweaks
# -----------------------
#
# This is another level that will eventually go aways once we wean ourselves off
# of OpenSSL and BCrypt.

# This will eventually go. OpenSSL and BCrypt disabled
ifeq ($(EVERCRYPT_CONFIG),everest)
HAND_WRITTEN_OPTIONAL_FILES :=
endif

# Customizations for Kaizala. No BCrypt, no Vale.
ifeq ($(EVERCRYPT_CONFIG),kaizala)
dist/gcc-compatible/Makefile.basic: \
  HAND_WRITTEN_OPTIONAL_FILES := $(filter-out %_bcrypt.c,$(HAND_WRITTEN_OPTIONAL_FILES))
dist/gcc-compatible/Makefile.basic: \
  HAND_WRITTEN_FILES := $(filter-out %_vale_stubs.c,$(HAND_WRITTEN_FILES))
dist/gcc-compatible/Makefile.basic: \
  VALE_ASMS :=
endif

# Actual KaRaMeL invocations
# --------------------------

.PRECIOUS: dist/%/Makefile.basic
dist/%/Makefile.basic: $(ALL_KRML_FILES) dist/LICENSE.txt \
  $(HAND_WRITTEN_FILES) $(HAND_WRITTEN_H_FILES) $(HAND_WRITTEN_OPTIONAL_FILES) $(VALE_ASMS) | old-extract-c
	mkdir -p $(dir $@)
	[ x"$(HACL_OLD_FILES)" != x ] && cp $(HACL_OLD_FILES) $(patsubst %.c,%.h,$(HACL_OLD_FILES)) $(dir $@) || true
	[ x"$(HAND_WRITTEN_FILES)$(HAND_WRITTEN_H_FILES)$(HAND_WRITTEN_OPTIONAL_FILES)" != x ] && cp $(HAND_WRITTEN_FILES) $(HAND_WRITTEN_H_FILES) $(HAND_WRITTEN_OPTIONAL_FILES) $(dir $@) || true
	[ x"$(HAND_WRITTEN_ML_BINDINGS)" != x ] && mkdir -p $(dir $@)/lib && cp $(HAND_WRITTEN_ML_BINDINGS) $(dir $@)lib/ || true
	[ x"$(HAND_WRITTEN_ML_GEN)" != x ] && mkdir -p $(dir $@)/lib_gen && cp $(HAND_WRITTEN_ML_GEN) $(dir $@)lib_gen/ || true
	[ x"$(VALE_ASMS)" != x ] && cp $(VALE_ASMS) $(dir $@) || true
	$(KRML) $(DEFAULT_FLAGS) \
	  -tmpdir $(dir $@) -skip-compilation \
	  $(filter %.krml,$^) \
	  -silent \
	  -ccopt -Wno-unused \
	  -warn-error @2@4-6@15@18@21+22 \
	  -fparentheses \
	  -fextern-c \
	  $(notdir $(HACL_OLD_FILES)) \
	  $(notdir $(HAND_WRITTEN_FILES)) \
	  -o libevercrypt.a
	echo "This code was generated with the following toolchain." > $(dir $@)/INFO.txt
	echo "F* version: $(shell cd $(FSTAR_HOME) && git rev-parse HEAD)" >> $(dir $@)/INFO.txt
	echo "KaRaMeL version: $(shell cd $(KRML_HOME) && git rev-parse HEAD)" >> $(dir $@)/INFO.txt
	echo "Vale version: $(shell cat $(VALE_HOME)/bin/.vale_version)" >> $(dir $@)/INFO.txt
	if [ "$*" == "wasm" ]; then touch $@; fi
	if [ x"$*" == xmozilla ]; then \
	  cp dist/Makefile.mozilla.config $(dir $@)/Makefile.config; \
	  cp dist/config.mozilla.h $(dir $@)/config.h; \
	fi

dist/evercrypt-external-headers/Makefile.basic: $(ALL_KRML_FILES)
	$(KRML) -silent \
	  -minimal \
	  -header $(HACL_HOME)/dist/LICENSE.txt \
	  -bundle EverCrypt+EverCrypt.AEAD+EverCrypt.AutoConfig2+EverCrypt.HKDF+EverCrypt.HMAC+EverCrypt.Hash+EverCrypt.Hash.Incremental+EverCrypt.Cipher+EverCrypt.Poly1305+EverCrypt.Chacha20Poly1305+EverCrypt.Curve25519=*[rename=EverCrypt] \
	  -library EverCrypt,EverCrypt.* \
	  -add-early-include '<inttypes.h>' \
	  -add-early-include '<stdbool.h>' \
	  -add-early-include '<krml/internal/types.h>' \
	  -add-early-include '<krml/internal/target.h>' \
	  -header dist/LICENSE.txt \
	  -skip-compilation \
	  -fextern-c \
	  -tmpdir $(dir $@) \
	  $^

# Auto-generates a single C test file. Note that this rule will trigger multiple
# times, for multiple KaRaMeL invocations in the test/ directory -- this may
# cause races on shared files (e.g. Makefile.basic, etc.) -- to be investigated.
# In the meanwhile, we at least try to copy the header for intrinsics just once.

.PRECIOUS: dist/test/c/%.c
dist/test/c/%.c: $(ALL_KRML_FILES)
	$(KRML) -silent \
	  -tmpdir $(dir $@) -skip-compilation \
	  -header $(HACL_HOME)/dist/LICENSE.txt \
	  -no-prefix $(subst _,.,$*) \
	  -library Hacl.P256,Hacl.K256.*,Hacl.Impl.*,EverCrypt,EverCrypt.* \
	  -fparentheses -fcurly-braces -fno-shadow \
	  -minimal -add-include '"krmllib.h"' \
	  -bundle '*[rename=$*]' $(KRML_EXTRA) $(filter %.krml,$^)

dist/test/c/Test.c: KRML_EXTRA=-add-early-include '"krml/internal/compat.h"'

dist/test/c/Hacl_Test_ECDSA.c: KRML_EXTRA=-drop Lib.IntTypes.Intrinsics -add-include '"lib_intrinsics.h"'

dist/test/c/Hacl_Test_K256.c: KRML_EXTRA=-drop Lib.IntTypes.Intrinsics -add-include '"lib_intrinsics.h"'

###################################################################################
# C Compilation (recursive make invocation relying on KaRaMeL-generated Makefile) #
###################################################################################

copy-krmllib:
	mkdir -p dist/karamel
	(cd $(KRML_HOME) && tar cvf - krmllib/dist/minimal include) | (cd dist/karamel && tar xf -)

compile-%: dist/Makefile.tmpl dist/configure dist/%/Makefile.basic | copy-krmllib
	cp $< dist/$*/Makefile
	(if [ -f dist/$*/libintvector.h -a $* != mozilla ]; then cp dist/configure dist/$*/configure; fi;)
	$(MAKE) -C dist/$*

###########################
# C tests (from F* files) #
###########################

ifeq ($(OS),Windows_NT)
OPENSSL_HOME	:= $(shell cygpath -u $(OPENSSL_HOME))
LDFLAGS		+= -lbcrypt
endif
LDFLAGS 	+= -L$(OPENSSL_HOME)

CFLAGS += -Wall -Wextra -g \
  -Wno-int-conversion -Wno-unused-parameter \
  -I$(OPENSSL_HOME)/include \
  -O3 -march=native -mtune=native -I$(KRML_HOME)/krmllib/dist/minimal \
  -I$(KRML_HOME)/include -Idist/gcc-compatible

# The C test files need the extracted headers to compile
dist/test/c/%.o: dist/test/c/%.c | compile-gcc-compatible
	$(call run-with-log,\
	  $(CC) $(CFLAGS) $< -c -o $@,[CC $*],$(call to-obj-dir,$@))

# FIXME there's a karamel error that generates a void* -- can't use -Werror
# Need the libraries to be present and compiled.
# Linking with full krmllib since tests may use TestLib, etc.
.PRECIOUS: %.exe
%.exe: %.o | compile-gcc-compatible
	$(call run-with-log,\
	  $(CC) $(CFLAGS) $(LDFLAGS) $^ -o $@ \
	    dist/gcc-compatible/libevercrypt.a -lcrypto $(LDFLAGS) \
	    $(KRML_HOME)/krmllib/dist/generic/libkrmllib.a \
	  ,[LD $*],$(call to-obj-dir,$@))

ifeq ($(OS),Windows_NT)
  LD_EXTRA = PATH="$(OPENSSL_HOME):$(shell cygpath -u $$(ocamlfind c -where))/../stublibs:$$PATH"
else ifeq ($(shell uname -s),Darwin)
  LD_EXTRA = DYLD_LIBRARY_PATH="$(OPENSSL_HOME)"
else
  LD_EXTRA = LD_LIBRARY_PATH="$(OPENSSL_HOME)"
endif

.PHONY: %.test
%.test: %.exe
	$(LD_EXTRA) $<

test-c-%: dist/test/c/%.test
	@

##########################
# C tests (from C files) #
##########################

test-handwritten: compile-gcc64-only compile-gcc-compatible
	$(LD_EXTRA) KRML_HOME="$(KRML_HOME)" \
	  LDFLAGS="$(LDFLAGS)" CFLAGS="$(CFLAGS)" \
	  $(MAKE) -C tests test

obj/vale_testInline.exe: vale/code/test/TestInline.c obj/vale_testInline.h
	$(CC) $(CFLAGS) $(LDFLAGS) $< -Iobj -o $@

vale_testInline: obj/vale_testInline.exe
	@echo "Testing Vale inline assembly printer"
	$<

#######################
# OCaml tests (specs) #
#######################

.PRECIOUS: dist/test/ml/%_AutoTest.ml
dist/test/ml/%_AutoTest.ml:
	mkdir -p $(dir $@)
	echo "if not ($*.test ()) then (print_endline \"$* failed\"; exit 1)" > $@

# Relying on the --extract argument of fstar --dep to have a reasonable
# over-approximation.
.PRECIOUS: dist/test/ml/%.exe
dist/test/ml/%.exe: $(ALL_CMX_FILES) dist/test/ml/%_AutoTest.ml
	$(OCAMLOPT) $^ -o $@

test-ml-%: dist/test/ml/%.exe
	$<

#################
# OCaml library #
#################

# This is good for users of HACL* who want to extract specs and link them
# against HACL*-extracted-to-ML

obj/libhaclml.cmxa: $(filter-out $(HACL_HOME)/obj/Meta_Interface.cmx,$(ALL_CMX_FILES))
	# JP: doesn't work because a PPX is prepended for some reason
	#ocamlfind mklib -o haclml -package fstarlib -g -I $(HACL_HOME)/obj $(addprefix $(HACL_HOME)/obj/*.,cmo cmx ml o)
	ocamlfind opt -a -o $@ -package fstarlib -g -I $(HACL_HOME)/obj $^


########
# Misc #
########

%/Makefile:
	echo "HACL_HOME=$(shell realpath . --relative-to $(dir $@))" > $@
	echo "include \$$(HACL_HOME)/Makefile.common" >> $@
