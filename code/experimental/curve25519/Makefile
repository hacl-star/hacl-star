include ../../../Makefile.include 

BN_FILES= \
	Hacl.Impl.Bignum.fst

verify: $(addsuffix -lax, $(BN_FILES))

KREMLIN_ARGS+= \
        -drop Prims,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128,Hacl.Endianness,Hacl.Cast,Hacl.Spec.*,Spec.*,Seq.* \
	-I ../../../specs -I ../../../specs/lib -I ../../../specs/lib/fst -I ../../../specs/lib/c \
        $(KREMLIN_TESTLIB)

c25519-c/out.krml: ../../../specs/lib/fst/Spec.Lib.IntTypes.fst ../../../specs/lib/fst/Spec.Lib.RawIntTypes.fst ../../../specs/lib/c/Spec.Lib.Loops.fst ../../../specs/lib/fst/Spec.Lib.IntBuf.fst  ../../../specs/lib/c/Spec.Lib.Endian.fst ../../../specs/lib/fst/Spec.Lib.IntBuf.LoadStore.fst $(BN_FILES)
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir c25519-c -skip-translation $^

c25519-c/Hacl_Impl_Bignum.c: c25519-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir c25519-c -skip-compilation \
	$^ -o $@

INCLUDE_C=-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/specs -I $(KREMLIN_HOME)/kremlib

CC=gcc-7 -pg -Os
CC := $(CC) $(INCLUDE_C)

BASE_OBJ = $(KREMLIN_HOME)/kremlib/testlib.o $(KREMLIN_HOME)/kremlib/kremlib.o

EXTRACTED= \
	Hacl_Impl_Bignum

%.o: %.c
	$(CC) -c $< -o $@

test-c25519.exe: $(addprefix c25519-c/,$(addsuffix .o, $(EXTRACTED))) $(BASE_OBJ)
	$(CC) -o $@ $^
	./test-c25519.exe

clean:
	rm -rf *.cmi *.cmo *.cmx *.o *~ *.out *.exe *-ml


