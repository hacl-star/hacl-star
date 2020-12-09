HACL_HOME=../..

all: dist/libpoly.a

# Defines rules for producing .checked, .krml, .depend, etc.
include ../../Makefile.local

CFLAGS += -I ../../../lib/c -I ../../lib/c -march=native -mtune=native -O3
export CFLAGS

dist/libpoly.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic


POLY_BUNDLE=-bundle Hacl.Impl.Poly=Hacl.Impl.Poly.Field

dist/Makefile.basic: $(filter-out %prims.krml,$(ALL_KRML_FILES))
	$(KRML) $^ -o libpoly.a $(BASE_FLAGS) $(POLY_BUNDLE) \
	-tmpdir dist \
	-skip-compilation

clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
