# An examplary local Makefile
# ---------------------------
#
# This demonstrates how to author a local Makefile that will allow for quick
# edit-compile-test cycles when working on a specific algorithm.
# - This is not under CI, so this Makefile may be broken.
# - This Makefile can *NOT* be run in parallel with another local Makefile.
# - In the case of Curve, this Makefile relies on an unverified connection with
#   Vale.

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: dist/curve64-ours.exe

HACL_HOME=../..

.depend: HACK
.PHONY: HACK
HACK:
	rm -rf $(HACL_HOME)/obj/Hacl_Impl_Curve25519_Field64_Vale.krml

# Defines rules for producing .checked, .krml, .depend, etc.
include ../Makefile.local

# CUSTOMIZE HERE: how to produce binary objects
dist:
	mkdir -p $@

# An archive with all the compiled code in this directory.
dist/libcurve.a: dist/curve25519-inline-tweaked.h dist/Makefile.basic | dist
	$(MAKE) -C dist -f Makefile.basic

dist/curve25519-inline-tweaked.h: $(HACL_HOME)/dist/vale/curve25519-inline.h | dist
	sed 's/_inline//g' $< > $@

$(HACL_HOME)/dist/vale/curve25519-inline.h:
	$(error Please run a full build first in $(HACL_HOME) so as to obtain $@)

# CUSTOMIZE HERE: if necessary, move the bundle from $(HACL_HOME)/Makefile to
# $(HACL_HOME)/Makefile.common; then, provide suitable compile flags.
dist/Makefile.basic: $(filter-out obj/prims.krml,$(ALL_KRML_FILES)) | dist
	$(KRML) $^ -o libcurve.a $(BASE_FLAGS) $(VALE_BUNDLES) $(CURVE_BUNDLE) \
	  -no-prefix 'Hacl.Impl.Curve25519.Field64.Vale' \
	  -add-include '"curve25519-inline-tweaked.h"' \
	  -add-include '<stdbool.h>' \
	  -tmpdir dist \
	  -ccopts -std=gnu11,-g,-O3 \
	  -skip-compilation

CFLAGS += -Idist -I$(KREMLIN_HOME)/include

KREMLIB_A=$(KREMLIN_HOME)/kremlib/dist/minimal/libkremlib.a

# CUSTOMIZE HERE: list the dependencies for each test (there may be multiple)
dist/curve64-ours.exe: $(HACL_HOME)/tests/curve64-ours.o dist/libcurve.a

%.exe:
	$(CC) $^ $(KREMLIB_A) -o $@
