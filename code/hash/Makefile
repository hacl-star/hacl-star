HACL_HOME     = ../..
FSTAR_HOME   ?= $(HACL_HOME)/dependencies/FStar
KREMLIN_HOME ?= $(HACL_HOME)/dependencies/kremlin
PROVIDER     ?= hacl

FSTAR ?= $(FSTAR_HOME)/bin/fstar.exe

KRML_BIN=$(KREMLIN_HOME)/_build/src/Kremlin.native
INCLUDES= -I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/specs \
  -I $(KREMLIN_HOME)/kremlib \
  -I $(HACL_HOME)/code/hash -I $(HACL_HOME)/other_providers/vale-glue
KRML=$(KRML_BIN) $(KREMLIN_ARGS) -verbose $(INCLUDES) \
  -drop Prims,FStar,Hacl.Cast,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128 \
  -drop Hacl.Spec.Endianness,Hacl.Endianness,Seq.Create,Spec.*,Hacl.Hash.SHA2_256.Lemmas \
  $(KREMLIN_HOME)/kremlib/testlib.c -tmpdir sha2-c \
  -add-include '"testlib.h"' -ccopt -march=native

HINTS_ENABLED= --use_hints


FSTARB=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
        --include $(HACL_HOME)/code/lib/kremlin --include $(KREMLIN_HOME)/kremlib \
         --include $(HACL_HOME)/specs  \
        $(HINTS_ENABLED) $(OTHERFLAGS)

FSTAR_CT=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
        --include $(HACL_HOME)/code/lib  --include $(KREMLIN_HOME)/kremlib \
        --include $(HACL_HOME)/specs

# Files for verification
SHA2_FILES = \
	Hacl.Hash.Lib.LoadStore.fst \
	Hacl.Hash.Lib.Create.fst \
	Hacl.Hash.SHA2_512.Lemmas.fst \
	Hacl.Hash.SHA2_512.fst \
	Hacl.Hash.SHA2_384.Lemmas.fst \
	Hacl.Hash.SHA2_384.fst \
	Hacl.Hash.SHA2_256.Lemmas.fst \
	Hacl.Hash.SHA2_256.fst

# Full typechecking against the transparent integer interface
%.fst-verify: %.fst
	$(FSTARB) $^

%.fsti-verify: %.fsti
	$(FSTARB) $^

# CI
all-ci: test

# Verification
all-verif: $(addsuffix -verify, $(SHA2_FILES)) # This is too costly for the CI

# Lax typechecking against the restricted integer interface
%.fst-ct: %.fst
	$(FSTAR_CT) --lax $^

all-ct: $(addsuffix -ct, $(SHA2_FILES))

# Extraction
extract-c: sha2-c/SHA2_256.c sha2-c/SHA2_384.c sha2-c/SHA2_512.c

test: test-sha2_256.exe test-sha2_384.exe test-sha2_512.exe

clean:
	rm -rf *~ *.exe *.exe.dSYM
	rm -rf sha2-c

extract-c: sha2-c/SHA2_256.c sha2-c/SHA2_512.c

sha2-c/out.krml: $(SHA2_FILES) SHA2_256.fst SHA2_512.fst Hacl.Test.SHA2_256.fst Hacl.Test.SHA2_512.fst
	$(KRML) -skip-translation $^

sha2-c/SHA2_256.c sha2-c/Hacl_Test_SHA2_256.c: sha2-c/out.krml
	$(KRML) $^ -skip-compilation -no-prefix Hacl.Test.SHA2_256 -bundle "SHA2_256=Hacl.Hash.Lib.Create,Hacl.Hash.Lib.LoadStore,Hacl.Hash.SHA2_256,SHA2_256"

sha2-c/SHA2_384.c sha2-c/Hacl_Test_SHA2_384.c: sha2-c/out.krml
	$(KRML) $^ -skip-compilation -no-prefix Hacl.Test.SHA2_384 -bundle "SHA2_384=Hacl.Hash.Lib.Create,Hacl.Hash.Lib.LoadStore,Hacl.Hash.SHA2_384,SHA2_384"

sha2-c/SHA2_512.c sha2-c/Hacl_Test_SHA2_512.c: sha2-c/out.krml
	$(KRML) $^ -skip-compilation -no-prefix Hacl.Test.SHA2_512 -bundle "SHA2_512=Hacl.Hash.Lib.Create,Hacl.Hash.Lib.LoadStore,Hacl.Hash.SHA2_512,SHA2_512"

CC := $(CC) $(INCLUDES)

%.o: %.c
	$(CC) -c $< -o $@

VALE_A := ../../other_providers/vale-glue/vale.a

$(VALE_A):
	$(MAKE) -C $(dir $@)

BASE_OBJ = $(VALE_A) sha2-c/Hacl_Config.o $(KREMLIN_HOME)/kremlib/testlib.o $(KREMLIN_HOME)/kremlib/kremlib.o

test-sha2_256.exe: sha2-c/SHA2_256.o sha2-c/Hacl_Test_SHA2_256.o sha2-c/Hacl_Config.o $(BASE_OBJ)
	$(CC) -o $@ $^

test-sha2_384.exe: sha2-c/SHA2_384.o sha2-c/Hacl_Test_SHA2_384.o sha2-c/Hacl_Config.o $(BASE_OBJ)
	$(CC) -o $@ $^

test-sha2_512.exe: sha2-c/SHA2_512.o sha2-c/Hacl_Test_SHA2_512.o sha2-c/Hacl_Config.o $(BASE_OBJ)
	$(CC) -o $@ $^
