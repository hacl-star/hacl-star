HACL_HOME=../../../

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).

CC = gcc-9.1
all: dist/libsparkle.a


# Defines rules for producing .checked, .krml, .depend, etc.
include ../../../Makefile.local

FSTAR_ROOTS += Hacl.Impl.Sparkle.fst

#BASE_FLAGS+= -funroll-loops 4

CFLAGS += -I ../../../lib/c -I . -march=native -mtune=native -O3
export CFLAGS

dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o libecdsa.a $(BASE_FLAGS)\
	  -tmpdir dist \
	  -fbuiltin-uint128 \
	  -funroll-loops 12 \
	  -skip-compilation

# An archive with all the compiled code in this directory.
# We don't want Hacl_Test_ECDSA.o to be included so we redefine OBJS
dist/libsparkle.a:dist/Hacl_Impl_Sparkle.o
	$(MAKE) -C dist -f Makefile.basic OBJS=$(notdir $^) $(notdir $@)
	
dist/%.o: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic $(notdir $@)

%.exe:
	$(CC) $(CFLAGS) -flto $^ -o $@

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean


