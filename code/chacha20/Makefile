# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: compile

test: all
	dist/chacha20-test.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include ../Makefile.local

CFLAGS += -I$(HACL_HOME)/lib/c -mavx -mavx2
export CFLAGS

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.
compile: dist/Makefile.basic
	$(MAKE) -C dist

dist/Makefile.basic: $(filter-out obj/prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o libchacha.a $(BASE_FLAGS) $(CHACHA20_BUNDLE) \
	  -tmpdir dist \
	  -ccopts -std=gnu11,-g,-O3 \
	  -add-include '"libintvector.h"' \
	  -skip-compilation
