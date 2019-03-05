# This Makefile covers all of the present repository (HACL* + Vale + EverCrypt)
# with the exclusion of legacy code found in secure_api, code/old and specs/old.
#
# From a high-level perspective, the coarse-grained dependency graph is:
#
#            merkle_tree
#                |
#             evercrypt                secure_api
#               /  \                      |
#           code   vale                code/old
#           /   \  /                      |
#         lib   specs                  specs/old
#
# This Makefile honors the following variables:
# - NOSHORTLOG=1 disables pretty (short) logs
# - NODEPEND=1 disables .depend re-generation (use for debugging only)
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
# - hacl-verify: non-staged target for reverifying HACL* files
# - verify: UNSTAGED, may only be invoked after a successful run of vale-fst,
#   verifies all .fst files, both hand-written and generated.
#
# To generate a Makefile for the interactive mode, use:
# - make foo/bar/Makefile
#
# CI targets:
# - ci: staged, runs all + test, without short logs (this repository's CI)
# - min-test: staged, runs only a subset of verification for the purposes of
#   F*'s extended CI

#########################
# Catching setup errors #
#########################

# This was needed once because of the shortest stem rule. I don't think it's
# needed anymore, but better be safe.
ifeq (3.81,$(MAKE_VERSION))
  $(error You seem to be using the OSX antiquated Make version. Hint: brew \
    install make, then invoke gmake instead of make)
endif

# Better error early.
ifeq (,$(VALE_HOME))
  $(error Please define VALE_HOME, possibly using cygpath -m on Windows)
endif

ifeq (,$(wildcard $(VALE_HOME)/bin/vale.exe))
  $(error $$VALE_HOME/bin/vale.exe does not exist (VALE_HOME=$(VALE_HOME)))
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
	$(MAKE) vale-fst
	FSTAR_DEPEND_FLAGS="--warn_error +285" $(MAKE) all_


all_: compile-compact compile-generic compile-compact-msvc \
  compile-evercrypt-external-headers compile-compact-c89 compile-coco \
  secure_api.old

# Any file in code/tests is taken to contain a `main` function.
# Any file in specs/tests is taken to contain a `test` function.
test:
	$(MAKE) vale-fst
	FSTAR_DEPEND_FLAGS="--warn_error +285" $(MAKE) test_

test_: test-c test-ml
test-c: $(subst .,_,$(patsubst %.fst,test-c-%,$(notdir $(wildcard code/tests/*.fst)))) \
  test-c-Test test-c-merkle_tree_test
test-ml: $(subst .,_,$(patsubst %.fst,test-ml-%,$(notdir $(wildcard specs/tests/*.fst))))

ci:
	NOSHORTLOG=1 $(MAKE) vale-fst
	FSTAR_DEPEND_FLAGS="--warn_error +285" NOSHORTLOG=1 $(MAKE) all_ test_

min-test:
	MIN_TEST=1 NOSHORTLOG=1 $(MAKE) vale-fst
	MIN_TEST=1 FSTAR_DEPEND_FLAGS="--warn_error +285" NOSHORTLOG=1 \
	  $(MAKE) min-test_

# Backwards-compat target
.PHONY: secure_api.old
secure_api.old:
	$(call run-with-log,$(MAKE) -C secure_api,[OLD-MAKE secure_api],obj/secure_api)

# So that this Makefile can also clean the previous directory layout. In the
# long run, TO_CLEAN should be able to go.
TO_CLEAN=$(foreach ext,checked checked.lax out cmd err time dump types.vaf krml cmx cmo cmi o d a,-or -iname '*.$(ext)')
clean:
	find . -iname '.depend*' $(TO_CLEAN) -delete
	rm -rf obj/*


#################
# Configuration #
#################

include Makefile.common

IMPORT_FSTAR_TYPES := $(VALE_HOME)/bin/importFStarTypes.exe
PYTHON3 := $(shell tools/findpython3.sh)
ifeq ($(OS),Windows_NT)
  MONO =
else
  MONO = mono
endif

ifeq ($(shell uname -s),Darwin)
  ifeq (,$(shell which gsed))
    $(error gsed not found; try brew install gnu-sed)
  endif
  SED := gsed
  ifeq (,$(shell which gtime))
    $(error gtime not found; try brew install gnu-time)
  endif
  TIME := gtime
else
  SED := sed
  TIME := /usr/bin/time
endif

ifneq ($(OS),Windows_NT)
ifneq ($(shell realpath $$(pwd)),$(shell realpath $$HACL_HOME))
  $(error HACL_HOME, currently set to $(HACL_HOME), does not seem to point to the current directory)
endif
endif


##########################
# Pretty-printing helper #
##########################

SHELL=/bin/bash

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
  $(TIME) -q -f '%E' -o $3.time sh -c "$(subst ",\",$1)" > $3.out 2> >( tee $3.err 1>&2 ); \
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
FSTAR_ROOTS = $(wildcard $(addsuffix /*.fsti,$(DIRS)) $(addsuffix /*.fst,$(DIRS))) \
  $(wildcard obj/*.fst) $(wildcard obj/*.fsti) # these two empty during the first stage

# Convenience target. Remember to run make vale-fst first.
verify: $(addsuffix .checked,$(FSTAR_ROOTS))

# We currently force regeneration of three depend files. This is long.

# If were are debugging (i.e. the files exist already); or within a restarting
# (NOT recursive) make invocation, meaning we are in the process of
# re-generating such files; then don't provide recipes for generating .depend
# files. (In the latter case, this would send make into an infinite loop.)

ifndef NODEPEND
ifndef MAKE_RESTARTS
# Note that the --extract argument only controls what is extracted for OCaml,
# meaning we can eliminate large chunks of the dependency graph, since we only
# need to run: Vale stuff, and HACL spec tests.
.fstar-depend-%: .FORCE
	$(call run-with-log,\
	  $(FSTAR_NO_FLAGS) --dep $* $(notdir $(FSTAR_ROOTS)) --warn_error '-285' $(FSTAR_DEPEND_FLAGS) \
	    --extract '* -Prims -LowStar -Lib.Buffer -Hacl -FStar +FStar.Endianness +FStar.Kremlin.Endianness -EverCrypt -MerkleTree -Vale.Tactics -FastHybrid_helpers -FastMul_helpers -FastSqr_helpers -FastUtil_helpers -TestLib -EverCrypt -MerkleTree -Test -Vale_memcpy -Vale.AsLowStar.Test -Lib.IntVector' > $@ && \
	  $(SED) -i 's!$(HACL_HOME)/obj/\(.*.checked\)!obj/\1!;s!/bin/../ulib/!/ulib/!g' $@ \
	  ,[FSTAR-DEPEND ($*)],$(call to-obj-dir,$@))

.vale-depend: .fstar-depend-make .FORCE
	$(call run-with-log,\
	  "$(PYTHON3)" tools/valedepend.py \
	    $(addprefix -include ,$(INCLUDES)) \
	    $(addprefix -in ,$(VALE_ROOTS)) \
	    -dep $< \
	    > $@ && \
	  $(SED) -i 's!$(HACL_HOME)/obj/\(.*.checked\)!obj/\1!g' $@ \
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
else ifeq ($(MAKECMDGOALS),all)
  SKIPDEPEND=1
else ifeq ($(MAKECMDGOALS),vale-verify)
  SKIPDEPEND=1
else ifeq ($(MAKECMDGOALS),ci)
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

# Always pass Operator.vaf as an -include to Vale, except for the file itself.
VALE_FLAGS = -include $(HACL_HOME)/vale/code/lib/util/Operator.vaf

obj/Operator.fst: VALE_FLAGS=

# Since valedepend generates "foo.fsti: foo.fst", ensure that the fsti is
# more recent than the fst (we don't know in what order vale.exe writes
# the files). (Actually, we know, hence this extra touch.)
%.fst:
	$(call run-with-log,\
	  $(MONO) $(VALE_HOME)/bin/vale.exe -fstarText -quickMods \
	    -typecheck -include $*.types.vaf \
	    $(VALE_FLAGS) \
	    -in $< -out $@ -outi $@i && touch -c $@i \
	  ,[VALE] $(notdir $*),$(call to-obj-dir,$@))

# A pseudo-target for the first stage.
vale-fst: $(VALE_FSTS)


################################################
# Verifying F* files to produce .checked files #
################################################

# A litany of file-specific options, replicating exactly what was in SConstruct
# before. TODO simplification would be good.
VALE_FSTAR_FLAGS_NOSMT=--z3cliopt smt.arith.nl=false \
  --z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 \
  --max_fuel 1 --max_ifuel 1 \
  --initial_ifuel 0 --use_extracted_interfaces true

VALE_FSTAR_FLAGS=$(VALE_FSTAR_FLAGS_NOSMT) \
  --smtencoding.elim_box true --smtencoding.l_arith_repr native \
  --smtencoding.nl_arith_repr wrapped

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

# By default Vale files don't use two phase tc
$(call only-for,$(HACL_HOME)/vale/%.checked): \
  FSTAR_FLAGS=$(VALE_FSTAR_FLAGS) --use_two_phase_tc false

# Except for the files in specs/ and code/
$(call only-for,$(HACL_HOME)/vale/specs/%.checked): \
  FSTAR_FLAGS=$(VALE_FSTAR_FLAGS)
$(call only-for,$(HACL_HOME)/vale/code/%.checked): \
  FSTAR_FLAGS=$(VALE_FSTAR_FLAGS)

# Except for the interop files, which apparently are ok with two phase TC.
$(call only-for,$(HACL_HOME)/vale/code/arch/x64/interop/%.checked): \
  FSTAR_FLAGS=$(shell echo $(VALE_FSTAR_FLAGS_NOSMT) | \
    sed 's/--z3cliopt smt.arith.nl=false//; \
      s/--z3cliopt smt.QI.EAGER_THRESHOLD=100//')

# Now the fst files coming from vaf files, which also don't work with two
# phase tc (VALE_FSTS is of the form obj/foobar.fst).
$(addsuffix .checked,$(VALE_FSTS)): \
  FSTAR_FLAGS=$(VALE_FSTAR_FLAGS) --use_two_phase_tc false

# Then a series of individual overrides.
obj/Interop.fst.checked: \
  FSTAR_FLAGS=$(shell echo $(VALE_FSTAR_FLAGS_NOSMT) | \
    sed 's/--use_extracted_interfaces true//; \
      s/--z3cliopt smt.QI.EAGER_THRESHOLD=100//') \
      --smtencoding.elim_box true

obj/BufferViewHelpers.fst.checked: \
  FSTAR_FLAGS=$(shell echo $(VALE_FSTAR_FLAGS_NOSMT) | \
    sed 's/--z3cliopt smt.arith.nl=false//;')

obj/Views.fst.checked: \
  FSTAR_FLAGS=$(shell echo $(VALE_FSTAR_FLAGS) | \
    sed 's/--smtencoding.nl_arith_repr wrapped/--smtencoding.nl_arith_repr native/;')

obj/Collections.Lists.fst.checked: \
  FSTAR_FLAGS=$(shell echo $(VALE_FSTAR_FLAGS) | \
    sed 's/--z3cliopt smt.QI.EAGER_THRESHOLD=100//')

obj/X64.Bytes_Semantics.fst.checked: \
  FSTAR_FLAGS=$(shell echo $(VALE_FSTAR_FLAGS) | \
    sed 's/--smtencoding.nl_arith_repr wrapped//; \
      s/--smtencoding.nl_arith_repr native//')

obj/X64.BufferViewStore.fst.checked: \
  FSTAR_FLAGS=$(VALE_FSTAR_FLAGS_NOSMT) --smtencoding.elim_box true

obj/X64.Poly1305.Util.fst.checked: \
  FSTAR_FLAGS=$(VALE_FSTAR_FLAGS_NOSMT)

obj/X64.Poly1305.Util.fsti.checked: \
  FSTAR_FLAGS=$(VALE_FSTAR_FLAGS_NOSMT)

obj/X64.Memory.fst.checked: \
  FSTAR_FLAGS=$(shell echo $(VALE_FSTAR_FLAGS_NOSMT) | \
    sed 's/--use_extracted_interfaces true//; \
      s/--z3cliopt smt.arith.nl=false//') \
      --smtencoding.elim_box true

obj/X64.Memory_Sems.fst.checked: \
  FSTAR_FLAGS=$(shell echo $(VALE_FSTAR_FLAGS_NOSMT) | \
    sed 's/--use_extracted_interfaces true//; \
      s/--z3cliopt smt.arith.nl=false//') \
      --smtencoding.elim_box true

obj/Vale.AsLowStar.Wrapper.fst.checked: \
  FSTAR_FLAGS=$(VALE_FSTAR_FLAGS)

obj/Vale.AsLowStar.Test.fst.checked: \
  FSTAR_FLAGS=$(VALE_FSTAR_FLAGS)

obj/Sha_stdcalls.fst.checked: \
  FSTAR_FLAGS=$(VALE_FSTAR_FLAGS)

obj/Simplify_Sha.fst.checked: \
  FSTAR_FLAGS=$(VALE_FSTAR_FLAGS)

obj/Fsub_stdcalls.fst.checked: \
  FSTAR_FLAGS=$(VALE_FSTAR_FLAGS)

obj/Fmul_stdcalls.fst.checked: \
  FSTAR_FLAGS=$(VALE_FSTAR_FLAGS)

obj/Fsqr_stdcalls.fst.checked: \
  FSTAR_FLAGS=$(VALE_FSTAR_FLAGS)

obj/Vale.Stdcalls.%.checked: \
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

# Convenience pseudo-targets
vale-verify:
	$(MAKE) vale-fst
	$(MAKE) vale-verify_

vale-verify_: \
  $(addsuffix .checked,$(VALE_FSTS)) \
  $(call only-for,$(HACL_HOME)/vale/%.checked) \

hacl-verify: $(call only-for,$(HACL_HOME)/code/%.checked)


############
# min-test #
############

min-test_: $(filter-out \
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

###############################################################################
# Extracting (checked files) to OCaml, producing executables, running them to #
# print ASM files                                                             #
###############################################################################

TAC = $(shell which tac >/dev/null 2>&1 && echo "tac" || echo "tail -r")

ALL_CMX_FILES = $(patsubst %.ml,%.cmx,$(shell echo $(ALL_ML_FILES) | $(TAC)))

ifeq ($(OS),Windows_NT)
  export OCAMLPATH := $(FSTAR_HOME)/bin;$(OCAMLPATH)
else
  export OCAMLPATH := $(FSTAR_HOME)/bin:$(OCAMLPATH)
endif

# Warning 8: this pattern-matching is not exhaustive.
# Warning 20: this argument will not be used by the function.
# Warning 26: unused variable
OCAMLOPT = ocamlfind opt -package fstarlib -linkpkg -g -I obj -w -8-20-26

.PRECIOUS: obj/%.cmx
obj/%.cmx: obj/%.ml
	$(call run-with-log,\
	  $(OCAMLOPT) -c $< -o $@ \
	  ,[OCAMLOPT-CMX] $(notdir $*),$(call to-obj-dir,$@))

obj/%.ml:
	$(call run-with-log,\
	  $(FSTAR) $(notdir $(subst .checked,,$<)) --codegen OCaml \
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

dist/vale/%-inline.c: obj/inline-vale-%.exe | dist/vale
	$< > $@

obj/vale-cpuid.exe: vale/code/lib/util/x64/CpuidMain.ml
obj/vale-aesgcm.exe: vale/code/crypto/aes/x64/Main.ml
obj/vale-sha256.exe: vale/code/crypto/sha/ShaMain.ml
obj/vale-curve25519.exe: vale/code/crypto/ecc/curve25519/Main25519.ml
obj/vale-poly1305.exe: vale/code/crypto/poly1305/x64/PolyMain.ml

obj/inline-vale-curve25519.exe: vale/code/crypto/ecc/curve25519/Inline25519.ml

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
    $(HACL_HOME)/secure_api/vale/asm/aes-*.S \
    $(HACL_HOME)/secure_api/vale/asm/aes-*.asm) \
  dist/vale/curve25519-inline.c

# A pseudo-target for generating just Vale assemblies
vale-asm: $(VALE_ASMS)


###########################################################################
# Extracting (checked files) to krml, then running kremlin to generate C. #
###########################################################################

.PRECIOUS: %.krml

obj/%.krml:
	$(call run-with-log,\
	  $(FSTAR) --codegen Kremlin \
	    --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	    $(notdir $(subst .checked,,$<)) && \
	  touch $@ \
	  ,[EXTRACT-KRML] $*,$@)

HAND_WRITTEN_C		= Lib.PrintBuffer Lib.RandomBuffer
HAND_WRITTEN_FILES 	= $(wildcard $(LIB_DIR)/c/*.c) \
  $(addprefix providers/evercrypt/c/evercrypt_,vale_stubs.c)
# Files in this list are not passed to kremlin, meaning that they don't end up
# in the Makefile.basic list of C source files. They're added manually in
# dist/Makefile (see ifneq tests).
HAND_WRITTEN_OPTIONAL_FILES = \
  $(addprefix providers/evercrypt/c/evercrypt_,openssl.c bcrypt.c)

# TODO: put all the Vale files under a single namespace to avoid this nonsense
#
# When extracting our libraries, we purposely don't distribute tests
DEFAULT_FLAGS		=\
  $(addprefix -library ,$(HACL_HAND_WRITTEN_C)) \
  -bundle Spec.*[rename=Hacl_Spec] \
  -bundle Lib.*[rename=Hacl_Lib] \
  -bundle Test,Test.*,Hacl.Test.* \
  -bundle EverCrypt.BCrypt \
  -bundle EverCrypt.OpenSSL \
  -bundle MerkleTree.Spec,MerkleTree.Spec.*,MerkleTree.New.High,MerkleTree.New.High.* \
  -bundle FStar.Tactics.CanonCommMonoid,FStar.Tactics.CanonCommSemiring,FStar.Tactics.CanonCommSwaps[rename=Unused] \
  -bundle FastUtil_helpers,FastHybrid_helpers,FastSqr_helpers,FastMul_helpers[rename=Unused2] \
  -bundle Opaque_s,Map16,Test.Vale_memcpy,Fast_defs,Interop_Printer,Memcpy[rename=Unused3] \
  -bundle X64.*,Arch.*,Words.*,Vale.*,Collections.*,Collections,SHA_helpers[rename=Unused4] \
  -bundle Prop_s,Types_s,Words_s,Views,AES_s,Workarounds,Math.*,Interop,TypesNative_s[rename=Unused5] \
  -bundle GF128_s,GF128,Poly1305.Spec_s,GCTR,GCTR_s,GHash_s,GCM_helpers,GHash[rename=Unused6] \
  -bundle AES_helpers,AES256_helpers,GCM_s,GCM,Interop_assumptions[rename=Unused7] \
  -bundle 'Interop,Interop.*,Fadd_inline,Fadd_stdcalls,Cpuid_stdcalls,Fswap_stdcalls,Fmul_stdcalls,Fsqr_stdcalls,Fsub_stdcalls,Poly_stdcalls,Sha_stdcalls[rename=Vale]' \
  -library 'Vale.Stdcalls.Cpuid' \
  -library 'Vale.Stdcalls.Fadd' \
  -library 'Vale.Stdcalls.Fmul' \
  -library 'Vale.Stdcalls.Fsqr' \
  -library 'Vale.Stdcalls.Fsub' \
  -library 'Vale.Stdcalls.Fswap' \
  -library 'Vale.Stdcalls.Poly' \
  -library 'Vale.Stdcalls.Sha' \
  -library 'Fadd_inline' \
  -no-prefix 'Vale.Stdcalls.Cpuid' \
  -no-prefix 'Vale.Stdcalls.Fadd' \
  -no-prefix 'Vale.Stdcalls.Fmul' \
  -no-prefix 'Vale.Stdcalls.Fsqr' \
  -no-prefix 'Vale.Stdcalls.Fsub' \
  -no-prefix 'Vale.Stdcalls.Fswap' \
  -no-prefix 'Vale.Stdcalls.Poly' \
  -no-prefix 'Vale.Stdcalls.Sha' \
  -no-prefix 'Fadd_inline' \
  -no-prefix 'EverCrypt.Vale' \
  -no-prefix 'MerkleTree.New.Low' \
  -no-prefix 'MerkleTree.New.Low.Serialization' \
  -fparentheses -fno-shadow -fcurly-braces

COMPACT_FLAGS	=\
  -bundle Hacl.Hash.MD5+Hacl.Hash.Core.MD5+Hacl.Hash.SHA1+Hacl.Hash.Core.SHA1+Hacl.Hash.SHA2+Hacl.Hash.Core.SHA2+Hacl.Hash.Core.SHA2.Constants=Hacl.Hash.*[rename=Hacl_Hash] \
  -bundle Hacl.Impl.SHA3+Hacl.SHA3=[rename=Hacl_SHA3] \
  -bundle LowStar.* \
  -bundle Prims,C.Failure,C,C.String,C.Loops,Spec.Loops,C.Endianness,FStar.*[rename=Hacl_Kremlib] \
  -bundle 'EverCrypt.Spec.*' \
  -bundle 'MerkleTree.*' \
  -bundle 'Test,Test.*,WindowsHack' \
  -bundle EverCrypt.Hash+EverCrypt.Hash.Incremental=[rename=EverCrypt_Hash] \
  -library EverCrypt.AutoConfig,EverCrypt.OpenSSL,EverCrypt.BCrypt \
  -minimal \
  -add-include '"kremlin/internal/types.h"' \
  -add-include '"kremlin/internal/target.h"' \
  -add-include '"kremlin/lowstar_endianness.h"' \
  -add-include '<string.h>'

# For the time being, we rely on the old extraction to give us self-contained
# files

.PHONY: old-%
old-%:
	$(call run-with-log,\
	  KOPTS=-verbose $(MAKE) -C code/old -f Makefile.old $* \
	  ,[OLD-MAKE $*],obj/old-$*)

HACL_OLD_FILES=\
  code/old/experimental/aesgcm/aesgcm-c/Hacl_AES.c \
  code/old/curve25519/x25519-c/Hacl_Curve25519.c \
  code/old/ed25519/ed25519-c/Hacl_Ed25519.c \
  code/old/salsa-family/chacha-c/Hacl_Chacha20.c \
  code/old/poly1305/poly-c/AEAD_Poly1305_64.c \
  code/old/poly1305/poly-c/Hacl_Poly1305_64.c \
  code/old/api/aead-c/Hacl_Chacha20Poly1305.c

dist/compact/Makefile.basic: KRML_EXTRA=$(COMPACT_FLAGS)

dist/compact-msvc/Makefile.basic: KRML_EXTRA=$(COMPACT_FLAGS) -falloca -ftail-calls

dist/compact-c89/Makefile.basic: \
  KRML_EXTRA=$(COMPACT_FLAGS) -fc89 -ccopt -std=c89 -ccopt -Wno-typedef-redefinition
dist/compact-c89/Makefile.basic: \
  HACL_OLD_FILES:=$(subst -c,-c89,$(HACL_OLD_FILES))

dist/coco/Makefile.basic: \
  KRML_EXTRA=$(COMPACT_FLAGS) \
    -bundle EverCrypt.AutoConfig2= \
    -bundle EverCrypt= \
    -bundle EverCrypt.Hacl \
    -bundle '\*[rename=EverCrypt_Misc]'

# The "coco" distribution is only optimized when EVERCRYPT_CONFIG=everest.
# Everest means: no openssl, no bcrypt
ifeq ($(EVERCRYPT_CONFIG),everest)
dist/coco/Makefile.basic: HAND_WRITTEN_OPTIONAL_FILES =
endif

# For Kaizala, no BCrypt, no Vale.
ifeq ($(EVERCRYPT_CONFIG),kaizala)
dist/compact/Makefile.basic: \
  HAND_WRITTEN_OPTIONAL_FILES := $(filter-out %_bcrypt.c,$(HAND_WRITTEN_OPTIONAL_FILES))
dist/compact/Makefile.basic: \
  HAND_WRITTEN_FILES := $(filter-out %_vale_stubs.c,$(HAND_WRITTEN_FILES))
dist/compact/Makefile.basic: \
  VALE_ASMS :=
endif

.PRECIOUS: dist/%/Makefile.basic
dist/%/Makefile.basic: $(ALL_KRML_FILES) dist/hacl-internal-headers/Makefile.basic \
  $(HAND_WRITTEN_FILES) $(HAND_WRITTEN_OPTIONAL_FILES) $(VALE_ASMS) | old-extract-c
	mkdir -p $(dir $@)
	cp $(HACL_OLD_FILES) $(patsubst %.c,%.h,$(HACL_OLD_FILES)) $(dir $@)
	cp $(HAND_WRITTEN_FILES) $(HAND_WRITTEN_OPTIONAL_FILES) dist/hacl-internal-headers/*.h $(dir $@)
	[ x"$(VALE_ASMS)" != x ] && cp $(VALE_ASMS) $(dir $@) || true
	$(KRML) $(DEFAULT_FLAGS) $(KRML_EXTRA) \
	  -tmpdir $(dir $@) -skip-compilation \
	  $(filter %.krml,$^) \
	  -silent \
	  -ccopt -Wno-unused \
	  -warn-error @4-6 \
	  -fparentheses \
	  $(notdir $(HACL_OLD_FILES)) \
	  $(notdir $(HAND_WRITTEN_FILES)) \
	  -o libevercrypt.a

# Auto-generates headers for the hand-written C files. If a signature changes on
# the F* side, hopefully this will ensure the C file breaks. Note that there is
# no conflict between the headers because this generates
# Lib_Foobar while the run above generates a single Hacl_Lib.
dist/hacl-internal-headers/Makefile.basic: $(ALL_KRML_FILES)
	$(KRML) -silent \
	  -tmpdir $(dir $@) -skip-compilation \
	  $(patsubst %,-bundle %=,$(HAND_WRITTEN_C)) \
	  $(patsubst %,-library %,$(HAND_WRITTEN_C)) \
	  -minimal -add-include '"kremlib.h"' \
	  -bundle '\*,WindowsBug' $^

dist/evercrypt-external-headers/Makefile.basic: $(ALL_KRML_FILES)
	$(KRML) -silent \
	  -minimal \
	  -bundle EverCrypt+EverCrypt.AutoConfig2+EverCrypt.HKDF+EverCrypt.HMAC+EverCrypt.Hash+EverCrypt.Hash.Incremental=*[rename=EverCrypt] \
	  -library EverCrypt,EverCrypt.* \
	  -add-include '<inttypes.h>' \
	  -add-include '<stdbool.h>' \
	  -add-include '<kremlin/internal/types.h>' \
	  -skip-compilation \
	  -tmpdir $(dir $@) \
	  $^

# Auto-generates a single C test file.
.PRECIOUS: dist/test/c/%.c
dist/test/c/%.c: $(ALL_KRML_FILES)
	$(KRML) -silent \
	  -tmpdir $(dir $@) -skip-compilation \
	  -no-prefix $(subst _,.,$*) \
	  -library Hacl,Lib,EverCrypt,EverCrypt.* \
	  -fparentheses -fcurly-braces -fno-shadow \
	  -minimal -add-include '"kremlib.h"' \
	  -bundle '*[rename=$*]' $(KRML_EXTRA) $^

dist/test/c/Test.c: KRML_EXTRA=-add-include '"kremlin/internal/compat.h"'


###################################################################################
# C Compilation (recursive make invocation relying on KreMLin-generated Makefile) #
###################################################################################

compile-%: dist/Makefile dist/%/Makefile.basic
	cp $< dist/$*/
	$(MAKE) -C dist/$*


###########
# C tests #
###########

ifeq ($(OS),Windows_NT)
OPENSSL_HOME	:= $(shell cygpath -u $(OPENSSL_HOME))
LDFLAGS		+= -lbcrypt
endif

dist/test/c/merkle_tree_test.c: secure_api/merkle_tree/test/merkle_tree_test.c
	mkdir -p $(dir $@)
	cp $< $(patsubst %.c,%.h,$<) $(dir $@)

# FIXME there's a kremlin error that generates a void* -- can't use -Werror
.PRECIOUS: dist/test/c/%.exe
dist/test/c/%.exe: dist/test/c/%.c compile-generic
	# Linking with full kremlib since tests may use TestLib, etc.
	$(call run-with-log,\
	  $(CC) -Wall -Wextra -Wno-infinite-recursion -Wno-int-conversion -Wno-unused-parameter \
	    -I $(dir $@) -I $(KREMLIN_HOME)/include -I $(OPENSSL_HOME)/include -I dist/generic \
	    -L$(OPENSSL_HOME) \
	    $< -o $@ \
	    dist/generic/libevercrypt.a -lcrypto $(LDFLAGS) \
	    $(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a \
	  ,[LD $*],$(call to-obj-dir,$@))

test-c-%: dist/test/c/%.exe
	LD_LIBRARY_PATH="$(OPENSSL_HOME)" DYLD_LIBRARY_PATH="$(OPENSSL_HOME)" \
	  PATH="$(OPENSSL_HOME):$(PATH)" $<


#######################
# OCaml tests (specs) #
#######################

.PRECIOUS: dist/test/ml/%_AutoTest.ml
dist/test/ml/%_AutoTest.ml:
	mkdir -p $(dir $@)
	echo "if not ($*.test ()) then (print_endline \"$* failed\"; exit 1)" > $@

# Relying on the --extract argument of fstar --dep to have a reasonable
# over-approximation.
dist/test/ml/%.exe: $(ALL_CMX_FILES) dist/test/ml/%_AutoTest.ml
	$(OCAMLOPT) $^ -o $@

test-ml-%: dist/test/ml/%.exe
	$<


########
# Misc #
########

%/Makefile:
	echo "HACL_HOME=$(shell realpath . --relative-to $(dir $@))" > $@
	echo "include \$$(HACL_HOME)/Makefile.common" >> $@
