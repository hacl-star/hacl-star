include ../../../Makefile.include 

RSA_FILES= \
	Hacl.Impl.Lib.fst \
	Hacl.Impl.Convert.fst \
	Hacl.Impl.Comparison.fst \
	Hacl.Impl.Addition.fst \
	Hacl.Impl.Multiplication.fst \
	Hacl.Impl.Shift.fst \
	Hacl.Impl.Montgomery.fst \
	Hacl.Impl.Exponentiation.fst \
	Hacl.Impl.MGF.fst \
	Hacl.Impl.RSA.fst \
	Hacl.RSAPSS.fst

verify: $(addsuffix -lax, $(RSA_FILES))

KREMLIN_ARGS+= \
        -drop Prims,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128,Hacl.Endianness,Hacl.Cast,Hacl.Spec.*,Spec.*,Seq.* \
        $(KREMLIN_TESTLIB)

rsa-c/out.krml: ../../../specs/lib/fst/Spec.Lib.IntTypes.fst ../../../specs/lib/fst/Spec.Lib.RawIntTypes.fst ../../../specs/lib/c/Spec.Lib.Loops.fst ../../../specs/lib/fst/Spec.Lib.IntBuf.fst  ../../../specs/lib/c/Spec.Lib.Endian.fst ../../../specs/lib/fst/Spec.Lib.IntBuf.LoadStore.fst Hacl.RSAPSS.fst Hacl.Test.RSA.fst
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir rsa-c -no-prefix 'Hacl.Test.RSA' \
        -I ../../../specs -I ../../../specs/lib -I ../../../specs/lib/fst  -I ../../../specs/lib/c \
	-bundle 'Hacl.RSAPSS=Hacl.Impl.*,Hacl.RSAPSS' \
        -skip-translation $^ -o $@

rsa-c/Hacl_RSAPSS.c: rsa-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir rsa-c -no-prefix 'Hacl.Test.RSA' \
	-bundle 'Hacl.RSAPSS=HAcl.Impl.*,Hacl.RSAPSS' \
	-skip-compilation $^ -o $@

test-rsa-kremlin.exe: rsa-c/out.krml
	mkdir -p rsa-c
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir rsa-c  -no-prefix 'Hacl.Test.RSA' \
	-I ../../../specs -I ../../../specs/lib -I ../../../specs/lib/fst -I ../../../specs/lib/c \
	-bundle 'Hacl.RSAPSS=HAcl.Impl.*,Hacl.RSAPSS' \
	$^ -o $@
	./$@

EXTRACTED= \
	Hacl_Impl_Lib \
	Hacl_Impl_Convert \
	Hacl_Impl_Comparison \
	Hacl_Impl_Addition \
	Hacl_Impl_Multiplication \
	Hacl_Impl_Shift \
	Hacl_Impl_Montgomery \
	Hacl_Impl_Exponentiation \
	Hacl_Impl_MGF \
	Hacl_Impl_RSA \
	Hacl_RSAPSS \
	Hacl_Test_RSA

$(addprefix rsa-c/,$(addsuffix .c, $(EXTRACTED))): rsa-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir rsa-c $^ -skip-compilation -no-prefix 'Hacl.Test.RSA'

INCLUDE_C=-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/specs -I $(KREMLIN_HOME)/kremlib

CC := $(CC) $(INCLUDE_C)

%.o: %.c
	$(CC) -c $< -o $@

BASE_OBJ = $(KREMLIN_HOME)/kremlib/testlib.o $(KREMLIN_HOME)/kremlib/kremlib.o $(HACL_HOME)/code/experimental/rsa/sha/Hacl_Hash_Lib_LoadStore.o $(HACL_HOME)/code/experimental/rsa/sha/Hacl_Hash_Lib_Create.o $(HACL_HOME)/code/experimental/rsa/sha/Hacl_Hash_SHA2_256.o $(HACL_HOME)/code/experimental/rsa/sha/SHA2_256.o

test-rsa.exe: $(addprefix rsa-c/,$(addsuffix .o, $(EXTRACTED))) $(BASE_OBJ)
	$(CC) -o $@ $^
	./test-rsa.exe
