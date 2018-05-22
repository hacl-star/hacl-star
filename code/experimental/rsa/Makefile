include ../../../Makefile.include

RSA_FILES= \
	Hacl.Impl.Lib.fst \
	Hacl.Impl.Convert.fst \
	Hacl.Impl.Comparison.fst \
	Hacl.Impl.Addition.fst \
	Hacl.Impl.Multiplication.fst \
	Hacl.Impl.Montgomery.fst \
	Hacl.Impl.Exponentiation.fst \
	Hacl.Impl.MGF.fst \
	Hacl.Impl.RSA.fst \
	Hacl.RSAPSS.fst

verify: $(addsuffix -lax, $(RSA_FILES))

KREMLIN_ARGS+=-verbose \
	-no-prefix C.Loops \
	-drop Prims,FStar,LowStar,C.Loops.Spec.Loops,Hacl.Cast,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128 \
	-drop Hacl.Spec.Endianness,Hacl.Endianness,Seq.Create,Spec.* \
	-drop Hacl.SHA256 \
	-add-early-include '"Hacl_SHA256.h"' -add-include '"kremlin/c_string.h"' \
	-ccopt -march=native

rsa-c/out.krml: ../../../specs/lib/fst/Spec.Lib.IntTypes.fst ../../../specs/lib/fst/Spec.Lib.RawIntTypes.fst ../../../specs/lib/c/Spec.Lib.Loops.fst ../../../specs/lib/fst/Spec.Lib.IntBuf.fst  ../../../specs/lib/c/Spec.Lib.Endian.fst ../../../specs/lib/fst/Spec.Lib.IntBuf.LoadStore.fst $(RSA_FILES) Hacl.Test.RSA.fst
	$(KREMLIN) $(KREMLIN_ARGS) -fsopt "--expose_interfaces" -tmpdir rsa-c \
	-I ../../../specs -I ../../../specs/lib -I ../../../specs/lib/fst -I $(KREMLIN_HOME)/include \
	-skip-translation $^

rsa-c/Hacl_RSAPSS.c: rsa-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir rsa-c -no-prefix 'Hacl.Test.RSA' -skip-compilation \
	-bundle 'Hacl.RSAPSS=Hacl.Impl.*,Hacl.RSAPSS' \
	$^ -o $@

rsa-c/Hacl_Test_RSA.c: rsa-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir rsa-c -no-prefix 'Hacl.Test.RSA' -skip-compilation \
	-bundle 'Hacl.RSAPSS=Hacl.Impl.*,Hacl.RSAPSS' \
	$^ -o $@

test-rsa-kremlin.exe: rsa-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir rsa-c  -no-prefix 'Hacl.Test.RSA' \
	-bundle 'Hacl.RSAPSS=Hacl.Impl.*,Hacl.RSAPSS' \
	$^ -o $@
	./$@

INCLUDE_C=-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/specs -I $(KREMLIN_HOME)/kremlib -I $(KREMLIN_HOME)/include -I $(HACL_HOME)/snapshots/hacl-c/ -I $(HACL_HOME)/code/experimental/rsa/include

CC := $(CC) $(INCLUDE_C)

BASE_OBJ=$(HACL_HOME)/specs/lib/c/Spec_Lib_Print.o $(HACL_HOME)/snapshots/hacl-c/Hacl_SHA2_256.o $(HACL_HOME)/code/experimental/rsa/include/Hacl_SHA256.o

EXTRACTED= \
	Hacl_RSAPSS \
	Hacl_Test_RSA

%.o: %.c
	$(CC) -c $< -o $@

test-rsa.exe: $(addprefix rsa-c/,$(addsuffix .o, $(EXTRACTED))) $(BASE_OBJ)
	$(CC) -o $@ $^

clean:
	rm -rf *~ *.exe *.exe.dSYM
	rm -rf rsa-c
