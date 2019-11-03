# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: dist/curve64-ours.exe

test: all
	dist/curve64-ours.exe

FSTAR_ROOTS = Hacl.Curve25519_64_Local.fst Hacl.Curve25519_64_Slow.fst Hacl.Curve25519_51.fst

# Defines rules for producing .checked, .krml, .depend, etc.
include ../../Makefile.local

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
dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES)) | dist
	$(KRML) $^ -o libcurve.a $(BASE_FLAGS) $(VALE_BUNDLES) $(CURVE_BUNDLE_LOCAL) \
	  -no-prefix 'Hacl.Impl.Curve25519.Field64.Local' \
	  -drop 'Hacl.Impl.Curve25519.Field64.Local' \
	  -add-include '"curve25519-inline-tweaked.h"' \
	  -add-include '<stdbool.h>' \
	  -add-include '"local.h"' \
	  -tmpdir dist \
	  -ccopts -std=gnu11,-g,-O3 \
	  -skip-compilation

# CUSTOMIZE HERE: list the dependencies for each test (there may be multiple)
dist/curve64-ours.exe: $(HACL_HOME)/tests/curve64-ours.o dist/libcurve.a

%.exe:
	$(CC) $^ $(KREMLIB_A) -o $@

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
