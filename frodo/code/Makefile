include ../../Makefile.include

KREMLIN_ARGS+=-verbose \
	-drop FStar,Prims,LowStar,C,C.*,C.Loops.Spec.Loops,Spec.*,Lib.*,WasmSupport \
	-drop Hacl.Cast,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128 \
	-drop Hacl.Spec.Endianness,Hacl.Endianness,Seq.Create \
	-drop Hacl.Impl.SHA2_256.Lemmas,Hacl.Impl.SHA2_384.Lemmas,Hacl.Impl.SHA2_512.Lemmas \
	-ccopt -march=native -warn-error +9


FSTAR_INCLUDES += --include ../spec

BASE_OBJ = ../../lib/c/Lib_PQ_Print.o $(HACL_HOME)/frodo/code/include/Hacl_Keccak.o $(LWEKE_HOME)/objs/sha3/fips202.o $(LWEKE_HOME)/tests/rng.o $(LWEKE_HOME)/objs/aes/aes_c.o $(LWEKE_HOME)/objs/aes/aes.o

HACL_LIBS = ../../lib/fst/Lib.IntTypes.fst ../../lib/fst/Lib.RawIntTypes.fst ../../lib/c/Lib.Loops.fst ../../lib/fst/Lib.PQ.Buffer.fst ../../lib/Lib.Print.fsti

LWEKE_HOME=$(HACL_HOME)/../Frodo/Reference_Implementation/reference/FrodoKEM-640

frodo-c/out.krml: $(HACL_LIBS) Hacl.Impl.PQ.Lib.fst Hacl.Keccak.fsti Hacl.Impl.Frodo.Params.fst Hacl.Impl.Frodo.Encode.fst Hacl.Impl.Frodo.Pack.fst Hacl.Impl.Frodo.fst test/Hacl.Test.Frodo.fst
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir frodo-c -no-prefix 'Hacl.Test.Frodo' -no-prefix 'Hacl.Impl.Frodo' \
	-I ../../specs -I ../spec -I ../../lib -I ../../lib/fst -I $(KREMLIN_HOME)/include \
	-skip-translation $^

frodo-c/Hacl_Test_Frodo.c: frodo-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) $(KREMLIN_TESTLIB) -tmpdir frodo-c -skip-compilation \
	-no-prefix 'Hacl.Test.Frodo' -no-prefix 'Hacl.Impl.Frodo' \
	-bundle 'Hacl.Impl.Frodo=Hacl.Impl.PQ.Lib,Hacl.Impl.Frodo,Hacl.Impl.Frodo.*' \
	-drop 'Hacl.Keccak' \
	-add-include '"extracted/C_Endianness.h"' \
	-add-include '"Hacl_Keccak.h"' \
	-add-include '"c/Lib_PQ_Print.h"' \
	$^ -o $@

#CC=gcc-7

CFLAGS += -O3 -march=native -mtune=native -funroll-loops

CFLAGS += -I $(KREMLIN_HOME)/include -I $(KREMLIN_HOME)/kremlib \
	  -I $(LWEKE_HOME)/sha3 -I $(HACL_HOME)/frodo/code/include \
	  -I $(HACL_HOME)/lib \
	  -Wall -Werror -Wno-parentheses -Wno-unused-value -Wno-int-to-pointer-cast -Wno-unused-variable

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

all: test

test-frodo.exe: frodo-c/Hacl_Test_Frodo.c frodo-c/Hacl_Impl_Frodo.c include/randombytes.c $(BASE_OBJ)
	$(CC) $(CFLAGS) -o $@ $^ -L $(KREMLIN_HOME)/kremlib/out -lkremlib

test: test-frodo.exe
	@echo Remember to set params_n = 64 in Hacl.Impl.Frodo.Params!
	./test-frodo.exe

AR=ar rcs

lib: $(BASE_OBJ) frodo-c/Hacl_Impl_Frodo.o include/randombytes.o
	$(AR) frodo-c/libfrodostar_for_testing.a $^
	ranlib frodo-c/libfrodostar_for_testing.a
	@echo Remember to set params_n = 640 in Hacl.Impl.Frodo.Params!

clean:
	rm -rf *~ *.exe *.exe.dSYM
	rm -rf frodo-c
