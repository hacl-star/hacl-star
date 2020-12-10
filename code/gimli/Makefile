HACL_HOME=../..

all: dist/gimli-test.exe

# Defines rules for producing .checked, .krml, .depend, etc.
include ../../Makefile.local

CFLAGS += -I ../../../lib/c -I ../../lib/c -march=native -mtune=native -O3
export CFLAGS

dist/libgimli.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic


dist/Makefile.basic: $(filter-out %prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o libgimli.a $(BASE_FLAGS) \
	-tmpdir dist \
	-no-prefix 'Hacl.Impl.Gimli' \
	-skip-compilation

dist/gimli-test.exe: gimli-test.o dist/libgimli.a

%.exe:
	$(CC) $(CFLAGS) $^ -o $@

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
