all: dist/FrodoKEM-64-test.exe

.PHONY: test
test: all
	dist/FrodoKEM-64-test.exe

include ../../Makefile.local

CFLAGS += -O3 -march=native -mtune=native -funroll-loops
CFLAGS += -fno-asynchronous-unwind-tables
export CFLAGS

FSTAR_ROOTS = Hacl.Frodo.KEM.fst
export FSTAR_ROOTS

BUNDLES = -bundle 'Hacl.SHA3=Hacl.Impl.SHA3,Hacl.SHA3'

BASE_FLAGS += $(BUNDLES)
BASE_FLAGS += -add-include '"kremlin/internal/target.h"'

dist:
	mkdir -p $@

dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES)) | dist
	$(KRML) $^ -o libfrodo.a \
	  -bundle Lib.RandomBuffer.System \
	  $(BASE_FLAGS) \
	  $(HACL_HOME)/lib/c/Lib_Memzero.c \
	  $(HACL_HOME)/lib/c/Lib_RandomBuffer_System.c \
	  $(FRODO_BUNDLE) \
	  -tmpdir dist \
	  -skip-compilation

dist/libfrodo.a: dist/Makefile.basic
	$(MAKE) -C dist -f Makefile.basic
	ranlib $@

$(HACL_HOME)/tests/FrodoKEM-64-test.o: dist/Makefile.basic

dist/FrodoKEM-64-test.exe: $(HACL_HOME)/tests/FrodoKEM-64-test.o dist/libfrodo.a

.PHONY: clean-c
clean-c:
	$(MAKE) -C dist/ -f Makefile.basic clean
