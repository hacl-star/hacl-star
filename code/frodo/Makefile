HACL_HOME=$(realpath ../..)

all: dist/FrodoKEM-64-test.exe

.PHONY: test
test: all
	dist/FrodoKEM-64-test.exe

include $(HACL_HOME)/Makefile.local

CFLAGS += -O3 -march=native -mtune=native -funroll-loops
CFLAGS += -fno-asynchronous-unwind-tables
CFLAGS += -I$(HACL_HOME)/lib/c
export CFLAGS

FSTAR_ROOTS = Hacl.Frodo64.fst Hacl.Frodo640.fst Hacl.Frodo976.fst Hacl.Frodo1344.fst
export FSTAR_ROOTS

BUNDLES = -bundle 'Hacl.SHA3=Hacl.Impl.SHA3,Hacl.SHA3'

BASE_FLAGS += $(BUNDLES)
BASE_FLAGS += -add-include '"krml/internal/target.h"'

dist:
	mkdir -p $@

dist/Makefile.basic: $(filter-out %/prims.krml,$(ALL_KRML_FILES)) | dist
	$(KRML) $^ -o libfrodo.a \
	  -bundle Lib.RandomBuffer.System \
	  $(BASE_FLAGS) \
	  $(HACL_HOME)/lib/c/Lib_Memzero0.c \
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
