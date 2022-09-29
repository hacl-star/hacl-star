HACL_HOME=$(realpath ../..)

# CUSTOMIZE HERE: determine what is the main target of this Makefile, e.g. a C
# test, a Low* test, or just a binary archive (like libcurve.a).
all: dist/Makefile.basic

test: all dist/blake2-test.exe
	dist/blake2-test.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include $(HACL_HOME)/Makefile.local

# CUSTOMIZE HERE: how to produce binary objects
# An archive with all the compiled code in this directory.

BLAKE2_BUNDLE= -bundle Hacl.Blake2b_32=Hacl.Impl.Blake2.\* \
  -bundle Hacl.Blake2s_32=Hacl.Impl.Blake2.\* \
  -bundle Hacl.Blake2s_128=Hacl.Impl.Blake2.\* \
  -bundle Hacl.Blake2b_256=Hacl.Impl.Blake2.\*


dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^  $(BASE_FLAGS) $(BLAKE2_BUNDLE) \
	  -funroll-loops 12 \
	  -fbuiltin-uint128 \
	  -tmpdir dist \
	  -skip-compilation \

dist/blake2-32-test.exe: dist/Makefile.basic $(HACL_HOME)/tests/blake2-32-test.c
	$(CC) -O3 -march=native -mtune=native -I $(HACL_HOME)/dist/gcc64-only -I dist -I $(HACL_HOME)/lib/c -I $(HACL_HOME)/dist/karamel/include -I $(HACL_HOME)/dist/karamel/krmllib/c -I $(HACL_HOME)/dist/karamel/krmllib/dist/minimal -I $(HACL_HOME)/tests $(HACL_HOME)/dist/gcc64-only/Lib_Memzero0.c $(HACL_HOME)/dist/gcc64-only/EverCrypt_AutoConfig2.c dist/Hacl_Blake2b_32.c  dist/Hacl_Blake2s_32.c $(HACL_HOME)/tests/blake2-32-test.c -o dist/blake2-32-test.exe

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
	rm -rf dist .output
