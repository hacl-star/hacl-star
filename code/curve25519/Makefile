# We reuse some definitions for F*, etc. but override the list of local
# directories we wish to have in scope to speed things up.
HACL_HOME=../..

ALL_HACL_DIRS=$(addprefix $(HACL_HOME)/,lib specs specs/lemmas code/meta) \
  $(addprefix $(HACL_HOME)/vale/specs/,defs hardware)

# This uses the definition of ALL_HACL_DIRS
include $(HACL_HOME)/Makefile.common

# All the files in the current directory ought to be verified.
FSTAR_ROOTS=$(wildcard *.fst *.fsti)

all: dist/curve64-ours.exe

# This is the right way to ensure the .depend file always gets re-built.
ifndef NODEPEND
ifndef MAKE_RESTARTS
.depend: .FORCE
	$(FSTAR_NO_FLAGS) --dep full $(notdir $(FSTAR_ROOTS)) > $@

.PHONY: .FORCE
.FORCE:
endif
endif

include .depend

# Producing .checked and .krml.
%.checked:
	$(FSTAR) $< --hint_file $(HACL_HOME)/hints/$(notdir $*).hints && \
	  touch -c $@

%.krml:
	$(FSTAR) --codegen Kremlin \
	    --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	    $(notdir $(subst .checked,,$<))

# Obtaining binary objects
dist:
	mkdir -p $@

dist/libcurve.a: dist/curve25519-inline-tweaked.h dist/Makefile.basic | dist
	$(MAKE) -C dist -f Makefile.basic

dist/curve25519-inline-tweaked.h: $(HACL_HOME)/dist/vale/curve25519-inline.h | dist
	sed 's/_inline//g' $< > $@

$(HACL_HOME)/dist/vale/curve25519-inline.h:
	$(error Please run a full build first in $(HACL_HOME) so as to obtain $@)

dist/Makefile.basic: $(filter-out obj/prims.krml,$(ALL_KRML_FILES)) | dist
	$(KRML) $^ -o libcurve.a $(BASE_FLAGS) $(VALE_BUNDLES) $(CURVE_BUNDLE) \
	  -no-prefix 'Hacl.Impl.Curve25519.Field64.Vale' \
	  -add-include '"curve25519-inline-tweaked.h"' \
	  -add-include '<stdbool.h>' \
	  -tmpdir dist \
	  -ccopts -std=gnu11,-g,-O3 \
	  -skip-compilation

# C tests
CFLAGS += -Idist -I$(KREMLIN_HOME)/include

KREMLIB_A=$(KREMLIN_HOME)/kremlib/dist/minimal/libkremlib.a

dist/curve64-ours.exe: $(HACL_HOME)/tests/curve64-ours.o dist/libcurve.a

%.exe:
	$(CC) $^ $(KREMLIB_A) -o $@
