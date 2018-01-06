include ../../../Makefile.include 

RSA_FILES= \
	Lib.fst \
	Convert.fst \
	Comparison.fst \
	Addition.fst \
	Multiplication.fst \
	Shift.fst \
	Montgomery.fst \
	Exponentiation.fst \
	MGF.fst \
	RSA.fst \
	Test.RSA.fst

verify: $(addsuffix -lax, $(RSA_FILES))

RSA_VERIFY= \
	Comparison.fst

verify-1: $(RSA_VERIFY)
	$(FSTAR_HOME)/bin/fstar.exe --query_stats $(OTHERFLAGS) $(FSTAR_INCLUDES) $^

KREMLIN_ARGS+= \
        -drop Prims,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128,Hacl.Endianness,Hacl.Cast,Hacl.Spec.*,Spec.*,Seq.* \
        $(KREMLIN_TESTLIB)

extract-c: rsa-c/RSA.c
test: test-rsa.exe

EXTRACTED = \
	Lib \
	Convert \
	Multiplication \
	Shift \
	Comparison \
	Addition \
	Montgomery \
	Exponentiation \
	MGF \
	RSA \
	Test_RSA

rsa-c/out.krml: ../../../specs/lib/fst/Spec.Lib.IntTypes.fst ../../../specs/lib/fst/Spec.Lib.RawIntTypes.fst ../../../specs/lib/c/Spec.Lib.Loops.fst ../../../specs/lib/fst/Spec.Lib.IntBuf.fst  ../../../specs/lib/c/Spec.Lib.Endian.fst ../../../specs/lib/fst/Spec.Lib.IntBuf.LoadStore.fst $(RSA_FILES) 
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir rsa-c \
        -I ../../../specs -I ../../../specs/lib -I ../../../specs/lib/fst  -I ../../../specs/lib/c \
        -skip-translation $^ -o $@

$(addprefix rsa-c/,$(addsuffix .c, $(EXTRACTED))): rsa-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir rsa-c $^ -skip-compilation -no-prefix 'Test.RSA'

test-rsa-kremlin.exe: rsa-c/out.krml
	mkdir -p rsa-c
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir rsa-c  -no-prefix Test.RSA \
	-I ../../../specs -I ../../../specs/lib -I ../../../specs/lib/fst -I ../../../specs/lib/c \
	$^ -o $@
	./$@

INCLUDE_C=-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/specs -I $(KREMLIN_HOME)/kremlib

CC := $(CC) $(INCLUDE_C)

%.o: %.c
	$(CC) -c $< -o $@

BASE_OBJ = $(KREMLIN_HOME)/kremlib/testlib.o $(KREMLIN_HOME)/kremlib/kremlib.o $(HACL_HOME)/code/experimental/rsa/sha/Hacl_Hash_Lib_LoadStore.o $(HACL_HOME)/code/experimental/rsa/sha/Hacl_Hash_Lib_Create.o $(HACL_HOME)/code/experimental/rsa/sha/Hacl_Hash_SHA2_256.o $(HACL_HOME)/code/experimental/rsa/sha/SHA2_256.o

test-rsa.exe: $(addprefix rsa-c/,$(addsuffix .o, $(EXTRACTED))) $(BASE_OBJ)
	$(CC) -o $@ $^
	./test-rsa.exe
