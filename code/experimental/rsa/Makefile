include ../../../Makefile.include 

RSA_FILES= \
	Lib.fst \
	Convert.fst \
	Multiplication.fst \
	Shift.fst \
	Comparison.fst \
	Addition.fst \
 	Division.fst \
	Exponentiation.fst \
	MGF.fst \
	RSA.fst \
	Test.RSA.fst
	
FSTAR_INCLUDES+=--include ../../hash

verify: $(addsuffix -lax, $(RSA_FILES))

RSA_VERIFY= \
	RSA.fst

verify-1: $(RSA_VERIFY)
	$(FSTAR_HOME)/bin/fstar.exe $(OTHERFLAGS) $(FSTAR_INCLUDES) $^

KREMLIN_ARGS+=-verbose \
	-tmpdir rsa-c \
	-I ../../../code/hash \
	-drop Prims,Hacl.Cast,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128 \
	-drop Hacl.Spec.Endianness,Hacl.Endianness,Seq.Create,Spec.* \
	-drop Hacl.Hash.SHA2_256.Lemmas \
	$(KREMLIN_TESTLIB) -ccopt -march=native

extract-c: rsa-c/RSA.c
test: test-rsa.exe

rsa-c/out.krml: $(RSA_FILES)
	$(KREMLIN) $(KREMLIN_ARGS) -skip-translation $^

EXTRACTED = \
	Lib \
	Hacl_Hash_Lib_LoadStore \
	Hacl_Hash_Lib_Create \
	Hacl_Hash_SHA2_256 \
	SHA2_256 \
	Convert \
	Multiplication \
	Shift \
	Comparison \
	Addition \
	Division \
	Exponentiation \
	MGF \
 	RSA \
 	Test_RSA

$(addprefix rsa-c/,$(addsuffix .c, $(EXTRACTED))): rsa-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) $^ -skip-compilation -no-prefix Test.RSA

test-rsa-kremlin.exe: rsa-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) $^ \
	-bundle RSA=Hacl.Hash.Lib.Create,Hacl.Hash.Lib.LoadStore,Hacl.Hash.SHA2_256,SHA2_256,Convert,Multiplication,Shift,Comparison,Addition,Division,Exponentiation,MGF,RSA \
	-no-prefix 'Test.RSA' -add-include '"RSA.h"' -o test-rsa-kremlin.exe
	./test-rsa-kremlin.exe

INCLUDE_C=-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/specs -I $(KREMLIN_HOME)/kremlib -I $(HACL_HOME)/code/hash

CC := $(CC) $(INCLUDE_C)

%.o: %.c
	$(CC) -c $< -o $@

BASE_OBJ = $(KREMLIN_HOME)/kremlib/testlib.o $(KREMLIN_HOME)/kremlib/kremlib.o

test-rsa.exe: $(addprefix rsa-c/,$(addsuffix .o, $(EXTRACTED))) $(BASE_OBJ)
	$(CC) -o $@ $^
	./test-rsa.exe