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

ifeq (3.81,$(MAKE_VERSION))
  $(error You seem to be using the OSX antiquated Make version. Hint: brew \
    install make, then hit invoke gmake instead of make)
endif

ifeq (,$(VALE_HOME))
  $(error Please define VALE_HOME)
endif

##########################
# Top-level entry points #
##########################

# This is a staged Makefile, because we first need to generate .fst files out of
# .vaf files in order to get a full dependency graph for the .fst files.
# This Makefile can be safely re-invoked with a different EVERCRYPT_CONFIG
# parameter to generate a different static specialization of EverCrypt.
all_:
	tools/blast-staticconfig.sh $(EVERCRYPT_CONFIG)
	$(MAKE) vaf-to-fst
	$(MAKE) all

debug:
	$(MAKE) vaf-to-fst
	$(MAKE) /home/jonathan/Code/fstar/bin/../ulib/CanonCommMonoid.fst.checked

all: compile-compact compile-generic compile-compact-msvc \
  compile-evercrypt-external-headers compile-compact-c89 compile-coco \
  # secure_api.old

# Any file in code/tests is taken to contain a `main` function.
# Any file in specs/tests is taken to contain a `test` function.
test: test-c test-ml
test-c: $(subst .,_,$(patsubst %.fst,test-c-%,$(notdir $(wildcard code/tests/*.fst)))) \
  test-c-Test test-c-merkle_tree_test
test-ml: $(subst .,_,$(patsubst %.fst,test-ml-%,$(notdir $(wildcard specs/tests/*.fst))))

ci:
	$(MAKE) vaf-to-fst
	$(MAKE) all test

# Backwards-compat target
.PHONY: secure_api.old
secure_api.old:
	$(MAKE) -C secure_api


#################
# Configuration #
#################

IMPORT_FSTAR_TYPES := $(VALE_HOME)/bin/importFStarTypes.exe
PYTHON3 := $(shell tools/findpython3.sh)
ifeq ($(OS),Windows_NT)
  MONO =
else
  MONO = mono
endif
SED := $(shell which gsed >/dev/null 2>&1 && echo gsed || echo sed)


####################################################
# Dependency graphs for Vale, then F* source files #
####################################################

# The set of .vaf files we want to translate to F*.
VALE_ROOTS = $(filter-out %.types.vaf,$(wildcard $(addsuffix /*.vaf,$(VALE_DIRS))))

# F* files stemming from Vale files
VALE_FSTS = $(patsubst %.vaf,%.fst,$(VALE_ROOTS))

# The complete set of F* files -- only meaningful in the second stage of this build.
FSTAR_ROOTS = $(wildcard $(addsuffix /*.fsti,$(DIRS)) $(addsuffix /*.fst,$(DIRS)))

include Makefile.common

# We currently force regeneration of three depend files... this is... long...
ifndef NODEPEND
ifndef MAKE_RESTARTS

# Note that the --extract argument only controls what is extracted for OCaml,
# meaning we can eliminate large chunks of the dependency graph, since we only
# need to run: Vale stuff, and HACL spec tests.
.fstar-depend-%: .FORCE
	@$(FSTAR_NO_FLAGS) --dep $* $(FSTAR_ROOTS) --extract '* -Prims -LowStar -Lib.Buffer -Hacl -FStar +FStar.Endianness +FStar.Kremlin.Endianness -EverCrypt -MerkleTree -Vale.Tactics -CanonCommMonoid -CanonCommSemiring -FastHybrid_helpers -FastMul_helpers -FastSqr_helpers -FastUtil_helpers -TestLib -EverCrypt -MerkleTree -Test -Vale_memcpy -Vale.AsLowStar.Test' > $@

.vale-depend: .fstar-depend-make .FORCE
	@$(PYTHON3) tools/valedepend.py \
	  $(addprefix -include ,$(INCLUDES)) \
	  $(addprefix -in ,$(VALE_ROOTS)) \
	  -dep $< \
	  > $@

.PHONY: .FORCE
.FORCE:
endif
endif

include .fstar-depend-full
include .vale-depend


#################################################
# First stage: compiling vaf files to fst files #
#################################################

%.dump: %.checked
	$(FSTAR) --dump_module $(subst prims,Prims,$(basename $(notdir $*))) \
          --print_implicits --print_universes --print_effect_args --print_full_names \
	  --print_bound_var_types --ugly --admit_smt_queries true \
	  $* > $@

%.types.vaf:
	$(MONO) $(IMPORT_FSTAR_TYPES) $(addprefix -in ,$^) -out $@

# Always pass Operator.vaf as an -include to Vale, except for the file itself.
VALE_FLAGS = -include $(HACL_HOME)/vale/code/lib/util/Operator.vaf

$(HACL_HOME)/vale/code/lib/util/Operator.fst: VALE_FLAGS=

%.fst:
	$(MONO) $(VALE_HOME)/bin/vale.exe -fstarText -quickMods \
	  -typecheck -include $*.types.vaf \
	  $(VALE_FLAGS) \
	  -in $< -out $@ -outi $@i

# A pseudo-target for the first stage.
vaf-to-fst: $(VALE_FSTS)

# When refresh is needed
append-gitignore:
	echo $(VALE_FSTS) | sed 's!$(HACL_HOME)!\n!g' >> .gitignore
	echo $(patsubst %.fst,%.fsti,$(VALE_FSTS)) | sed 's!$(HACL_HOME)!\n!g' >> .gitignore


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

# By default Vale files don't use two phase tc
$(HACL_HOME)/vale/%.checked: \
  FSTAR_FLAGS=$(VALE_FSTAR_FLAGS) --use_two_phase_tc false

# Except for the files in specs/ and code/
$(HACL_HOME)/vale/specs/%.checked: \
  FSTAR_FLAGS=$(VALE_FSTAR_FLAGS)
$(HACL_HOME)/vale/code/%.checked: \
  FSTAR_FLAGS=$(VALE_FSTAR_FLAGS)

# Except for the interop files, which apparently are ok with two phase TC.
$(HACL_HOME)/vale/code/arch/x64/interop/%.checked: \
  FSTAR_FLAGS=$(shell echo $(VALE_FSTAR_FLAGS_NOSMT) | \
    sed 's/--z3cliopt smt.arith.nl=false//; \
      s/--z3cliopt smt.QI.EAGER_THRESHOLD=100//')

# Except for the files coming from vaf files, which also don't work with two
# phase tc.
$(patsubst %.fst,%.fst.checked,$(VALE_FSTS)) \
$(patsubst %.fst,%.fsti.checked,$(VALE_FSTS)): \
  FSTAR_FLAGS=$(VALE_FSTAR_FLAGS) --use_two_phase_tc false

# Then a series of individual overrides.
$(HACL_HOME)/vale/code/arch/x64/Interop.fst.checked: \
  FSTAR_FLAGS=$(shell echo $(VALE_FSTAR_FLAGS_NOSMT) | \
    sed 's/--use_extracted_interfaces true//; \
      s/--z3cliopt smt.QI.EAGER_THRESHOLD=100//') \
      --smtencoding.elim_box true

$(HACL_HOME)/vale/code/lib/util/BufferViewHelpers.fst.checked: \
  FSTAR_FLAGS=$(shell echo $(VALE_FSTAR_FLAGS_NOSMT) | \
    sed 's/--z3cliopt smt.arith.nl=false//;')

$(HACL_HOME)/vale/code/arch/x64/Views.fst.checked: \
  FSTAR_FLAGS=$(shell echo $(VALE_FSTAR_FLAGS) | \
    sed 's/--smtencoding.nl_arith_repr wrapped/--smtencoding.nl_arith_repr native/;')

$(HACL_HOME)/vale/code/lib/collections/Collections.Lists.fst.checked: \
  FSTAR_FLAGS=$(shell echo $(VALE_FSTAR_FLAGS) | \
    sed 's/--z3cliopt smt.QI.EAGER_THRESHOLD=100//')

$(HACL_HOME)/vale/code/arch/x64/X64.Bytes_Semantics.fst.checked: \
  FSTAR_FLAGS=$(shell echo $(VALE_FSTAR_FLAGS) | \
    sed 's/--smtencoding.nl_arith_repr wrapped//; \
      s/--smtencoding.nl_arith_repr native//')

$(HACL_HOME)/vale/code/arch/x64/X64.BufferViewStore.fst.checked: \
  FSTAR_FLAGS=$(VALE_FSTAR_FLAGS_NOSMT) --smtencoding.elim_box true

$(HACL_HOME)/vale/code/crypto/poly1305/x64/X64.Poly1305.Util.fst.checked: \
  FSTAR_FLAGS=$(VALE_FSTAR_FLAGS_NOSMT)

$(HACL_HOME)/vale/code/crypto/poly1305/x64/X64.Poly1305.Util.fsti.checked: \
  FSTAR_FLAGS=$(VALE_FSTAR_FLAGS_NOSMT)

$(HACL_HOME)/vale/code/arch/x64/X64.Memory.fst.checked: \
  FSTAR_FLAGS=$(shell echo $(VALE_FSTAR_FLAGS_NOSMT) | \
    sed 's/--use_extracted_interfaces true//; \
      s/--z3cliopt smt.arith.nl=false//') \
      --smtencoding.elim_box true

$(HACL_HOME)/vale/code/arch/x64/X64.Memory_Sems.fst.checked: \
  FSTAR_FLAGS=$(shell echo $(VALE_FSTAR_FLAGS_NOSMT) | \
    sed 's/--use_extracted_interfaces true//; \
      s/--z3cliopt smt.arith.nl=false//') \
      --smtencoding.elim_box true

# The actual default invocation. Note that the FSTAR_FLAGS= definition allows
# making sure prerequisites of a given rule (e.g. CanonCommMonoid) don't inherit
# the variable assignment of their parent rule.
%.checked: FSTAR_FLAGS=
%.checked:
	$(FSTAR) $(FSTAR_FLAGS) $< && \
	touch $@


###############################################################################
# Extracting (checked files) to OCaml, producing executables, running them to #
# print ASM files                                                             #
###############################################################################

include $(FSTAR_HOME)/ulib/ml/Makefile.include

TAC = $(shell which tac >/dev/null 2>&1 && echo "tac" || echo "tail -r")

ALL_CMX_FILES = $(patsubst %.ml,%.cmx,$(shell echo $(ALL_ML_FILES) | $(TAC)))

OCAMLOPT += -I $(OUTPUT_DIR)

.PRECIOUS: %.cmx
%.cmx: %.ml
	$(OCAMLOPT) -c $< -o $@

$(OUTPUT_DIR)/%.ml:
	$(FSTAR) $(subst .checked,,$<) --codegen OCaml --extract_module $(subst .fst.checked,,$(notdir $<))

dist/vale/%-x86_64-mingw.S: dist/vale/%.exe
	$< GCC Win > $@
	$(SED) 's/_stdcall//' -i $@

dist/vale/%-x86_64-msvc.S: dist/vale/%.exe
	$< MASM Win > $@
	$(SED) 's/_stdcall//' -i $@

dist/vale/%-x86_64-linux.S: dist/vale/%.exe
	$< GCC Linux > $@
	$(SED) 's/_stdcall//' -i $@

dist/vale/%-x86_64-darwin.S: dist/vale/%.exe
	$< GCC MacOS > $@
	$(SED) 's/_stdcall//' -i $@

dist/vale/cpuid.exe: vale/code/lib/util/x64/CpuidMain.ml
dist/vale/aesgcm.exe: vale/code/crypto/aes/x64/Main.ml
dist/vale/sha256.exe: vale/code/crypto/sha/ShaMain.ml
dist/vale/curve25519.exe: vale/code/crypto/ecc/curve25519/Main25519.ml

dist/vale/%.exe: $(ALL_CMX_FILES) vale/code/lib/util/CmdLineParser.ml
	mkdir -p $(dir $@)
	$(OCAMLOPT) $^ -o $@ -I vale/code/lib/util

# The ones in secure_api are legacy and should go.
VALE_ASMS = $(foreach P,cpuid aesgcm sha256 curve25519,\
  $(addprefix dist/vale/,$P-x86_64-mingw.S $P-x86_64-msvc.S $P-x86_64-linux.S $P-x86_64-darwin.S)) \
  $(wildcard \
    $(HACL_HOME)/secure_api/vale/asm/aes-*.S \
    $(HACL_HOME)/secure_api/vale/asm/aes-*.asm)

# A pseudo-target for generating just Vale assemblies
vale-asm: $(VALE_ASMS)

###########################################################################
# Extracting (checked files) to krml, then running kremlin to generate C. #
###########################################################################

.PRECIOUS: %.krml

$(OUTPUT_DIR)/%.krml:
	$(FSTAR) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

HAND_WRITTEN_C		= Lib.PrintBuffer Lib.RandomBuffer
HAND_WRITTEN_FILES 	= $(wildcard $(LIB_DIR)/c/*.c) \
  $(addprefix providers/evercrypt/c/evercrypt_,vale_stubs.c)
# Files in this list are not passed to kremlin, meaning that they don't end up
# in the Makefile.basic list of C source files. They're added manually in
# dist/Makefile (see ifneq tests).
HAND_WRITTEN_OPTIONAL_FILES = \
  $(addprefix providers/evercrypt/c/evercrypt_,openssl.c bcrypt.c bytes.c)

# TODO: put all the Vale files under a single namespace to avoid this nonsense
# TODO: actually remove EverCrypt.Bytes rather than disabling it here.
#
# When extracting our libraries, we purposely don't distribute tests
DEFAULT_FLAGS		=\
  $(addprefix -library ,$(HACL_HAND_WRITTEN_C)) \
  -bundle Spec.*[rename=Hacl_Spec] \
  -bundle Lib.*[rename=Hacl_Lib] \
  -bundle Test,Test.*,Hacl.Test.* \
  -bundle EverCrypt.Bytes \
  -bundle EverCrypt.BCrypt \
  -bundle EverCrypt.OpenSSL \
  -bundle MerkleTree.Spec,MerkleTree.Spec.*,MerkleTree.New.High,MerkleTree.New.High.* \
  -bundle CanonCommMonoid,CanonCommSemiring,CanonCommSwaps[rename=Unused] \
  -bundle FastUtil_helpers,FastHybrid_helpers,FastSqr_helpers,FastMul_helpers[rename=Unused2] \
  -bundle Opaque_s,Map16,Test.Vale_memcpy,Fast_defs,Interop_Printer,Memcpy[rename=Unused3] \
  -bundle X64.*,Arch.*,Words.*,Vale.*,Collections.*,Collections,SHA_helpers,Interop,Interop.*[rename=Unused4] \
  -bundle Prop_s,Types_s,Words_s,Views,AES_s,Workarounds,Math.*,Interop,TypesNative_s[rename=Unused5] \
  -bundle GF128_s,GF128,Poly1305.Spec_s,GCTR,GCTR_s,GHash_s,GCM_helpers,GHash[rename=Unused6] \
  -bundle AES_helpers,AES256_helpers,GCM_s,GCM,Interop_assumptions[rename=Unused7] \
  -bundle 'Check_aesni_stdcall,Check_sha_stdcall,Sha_update_bytes_stdcall[rename=Vale]' \
  -library 'Sha_stdcalls' \
  -library 'Poly_stdcalls' \
  -library 'Fast_stdcalls' \
  -library 'Cpuid_stdcalls' \
  -no-prefix 'Sha_stdcalls' \
  -no-prefix 'Poly_stdcalls' \
  -no-prefix 'Fast_stdcalls' \
  -no-prefix 'Cpuid_stdcalls' \
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
  -library EverCrypt.Bytes,EverCrypt.AutoConfig,EverCrypt.OpenSSL,EverCrypt.BCrypt \
  -minimal \
  -add-include '"kremlin/internal/types.h"' \
  -add-include '"kremlin/internal/target.h"' \
  -add-include '"kremlin/c_endianness.h"' \
  -add-include '<string.h>'

# For the time being, we rely on the old extraction to give us self-contained
# files

.PHONY: old-%
old-%:
	$(MAKE) -C code/old -f Makefile.old $*

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
ifeq ($(EVERCRYPT_CONFIG),everest)
dist/coco/Makefile.basic: HAND_WRITTEN_OPTIONAL_FILES =
endif

.PRECIOUS: dist/%/Makefile.basic
dist/%/Makefile.basic: $(ALL_KRML_FILES) dist/hacl-internal-headers/Makefile.basic \
  $(HAND_WRITTEN_FILES) $(VALE_ASMS) | old-extract-c
	mkdir -p $(dir $@)
	cp $(HACL_OLD_FILES) $(patsubst %.c,%.h,$(HACL_OLD_FILES)) $(dir $@)
	cp $(HAND_WRITTEN_FILES) $(HAND_WRITTEN_OPTIONAL_FILES) dist/hacl-internal-headers/*.h $(dir $@)
	cp $(VALE_ASMS) $(dir $@)
	$(KRML) $(DEFAULT_FLAGS) $(KRML_EXTRA) \
	  -tmpdir $(dir $@) -skip-compilation \
	  $(filter %.krml,$^) \
	  -ccopt -Wno-unused \
	  -warn-error @4 \
	  -fparentheses \
	  $(notdir $(HACL_OLD_FILES)) \
	  $(notdir $(HAND_WRITTEN_FILES)) \
	  -o libevercrypt.a

# Auto-generates headers for the hand-written C files. If a signature changes on
# the F* side, hopefully this will ensure the C file breaks. Note that there is
# no conflict between the headers because this generates
# Lib_Foobar while the run above generates a single Hacl_Lib.
dist/hacl-internal-headers/Makefile.basic: $(ALL_KRML_FILES)
	$(KRML) \
	  -tmpdir $(dir $@) -skip-compilation \
	  $(patsubst %,-bundle %=,$(HAND_WRITTEN_C)) \
	  $(patsubst %,-library %,$(HAND_WRITTEN_C)) \
	  -minimal -add-include '"kremlib.h"' \
	  -bundle '\*,WindowsBug' $^

dist/evercrypt-external-headers/Makefile.basic: $(ALL_KRML_FILES)
	$(KRML) \
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
	$(KRML) \
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

# Backwards-compat, remove
ifneq (,$(MLCRYPTO_HOME))
OPENSSL_HOME 	= $(MLCRYPTO_HOME)/openssl
endif

dist/test/c/merkle_tree_test.c: secure_api/merkle_tree/test/merkle_tree_test.c
	mkdir -p $(dir $@)
	cp $< $(patsubst %.c,%.h,$<) $(dir $@)

# FIXME there's a kremlin error that generates a void* -- can't use -Werror
.PRECIOUS: dist/test/c/%.exe
dist/test/c/%.exe: dist/test/c/%.c compile-generic
	# Linking with full kremlib since tests may use TestLib, etc.
	$(CC) -Wall -Wextra -Wno-infinite-recursion -Wno-int-conversion -Wno-unused-parameter \
	  -I $(dir $@) -I $(KREMLIN_HOME)/include -I $(OPENSSL_HOME)/include -I dist/generic \
	  -L$(OPENSSL_HOME) \
	  $< -o $@ \
	  dist/generic/libevercrypt.a -lcrypto \
	  $(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a

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
