HACL_HOME?=../../..
include ../Makefile.include

# Files for verification
SHA2_FILES = \
	Hacl.Hash.Lib.LoadStore.fst \
	Hacl.Hash.Lib.Create.fst \
	Hacl.Impl.SHA2_512.Lemmas.fst \
	Hacl.Impl.SHA2_512.fst \

SLOW=
BROKEN=

ct: $(addsuffix -lax, $(SHA2_FILES))
# Excluding slow or broken files from the CI run
ci: $(addsuffix -verify, $(filter-out $(SLOW) $(BROKEN), $(SHA2_FILES)))
verify: $(addsuffix -verify, $(filter-out $(SLOW) $(BROKEN), $(SHA2_FILES)))
hints: $(addsuffix .hints, $(SHA2_FILES))
all-ct: ct
all-ver: verify
all-ci: ci
all-hints: hints

KREMLIN_ARGS+=-verbose \
	$(KREMLIN_TESTLIB) -ccopt -march=native

MODULES=$(foreach N,512,Hacl.SHA2_$(N) Hacl.Impl.SHA2_$(N))
TESTMODS=$(foreach N,512,Hacl.Test.SHA2_$(N))

extract-c: $(foreach N,512,sha2-c-test/Hacl_Test_SHA2_$(N).c sha2-c/Hacl_SHA2_$(N).c)
test: test-sha2_512.exe

SPACE=$(empty) $(empty)
COMMA=,

sha2-c/out.krml: $(SHA2_FILES) $(addsuffix .fst,$(MODULES)) $(addsuffix .fst,$(TESTMODS))
	$(KREMLIN) $(KREMLIN_ARGS) -I interfaces -tmpdir sha2-c -skip-translation $^

sha2-c/Hacl_SHA2_%.c: sha2-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir sha2-c -skip-compilation \
	 -minimal -add-include '"kremlib.h"' -bundle "Hacl.SHA2_$*=*" \
	 $^ -o $@

# Until the target above writes to disjoint sets of files with its different
# invocations, this Makefile cannot be run in parallel. This has caused sadness
# on CI because of concurrent writes to the same file that leave invalid C
# syntax in there.
.NOTPARALLEL:

sha2-c-test/Hacl_Test_SHA2_%.c: sha2-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir sha2-c-test -skip-compilation -no-prefix Hacl.Test.SHA2_$* \
	-drop $(subst $(SPACE),$(COMMA),$(filter-out Hacl.Impl.SHA2_$*,$(filter-out Hacl.SHA2_$*,$(MODULES)))) \
	-drop $(subst $(SPACE),$(COMMA),$(filter-out Hacl.Test.SHA2_$*,$(TESTMODS))) \
	-drop Prims,LowStar,C.Loops.Spec.Loops,Spec.* \
	-drop Hacl.Cast,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128 \
	-drop Hacl.Spec.Endianness,Hacl.Endianness,Seq.Create \
	-drop Hacl.Impl.SHA2_256.Lemmas,Hacl.Impl.SHA2_384.Lemmas,Hacl.Impl.SHA2_512.Lemmas,WasmSupport \
	-bundle "Hacl.SHA2_$*=Hacl.Hash.Lib.Create,Hacl.Hash.Lib.LoadStore,Hacl.Impl.SHA2_$*,Hacl.SHA2_$*" \
	$^ -o $@

test-sha2_%.exe: sha2-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir sha2-$*-c -no-prefix Hacl.Test.SHA2_$* \
	-drop $(subst $(SPACE),$(COMMA),$(filter-out Hacl.Impl.SHA2_$*,$(filter-out Hacl.SHA2_$*,$(MODULES)))) \
	-drop $(subst $(SPACE),$(COMMA),$(filter-out Hacl.Test.SHA2_$*,$(TESTMODS))) \
	-drop Prims,LowStar,C.Loops.Spec.Loops,Spec.* \
	-drop Hacl.Cast,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128 \
	-drop Hacl.Spec.Endianness,Hacl.Endianness,Seq.Create \
	-drop Hacl.Impl.SHA2_256.Lemmas,Hacl.Impl.SHA2_384.Lemmas,Hacl.Impl.SHA2_512.Lemmas,WasmSupport \
	-bundle "Hacl.SHA2_$*=Hacl.Hash.Lib.Create,Hacl.Hash.Lib.LoadStore,Hacl.Impl.SHA2_$*,Hacl.SHA2_$*" \
	$^ -o $@
	./$@

# The following 'native' test targets use CC and CFLAGS, which may be different from the compiler and
# flags that Kremlin uses/chooses. So, use with care.

test-native: test-native-sha2_256.exe test-native-sha2_512.exe

BASE_OBJ=$(VALE_A) sha2-c/testlib.o sha2-c/kremlib.o
$(BASE_OBJ): sha2-c/out.krml

CFLAGS=-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/specs -I $(KREMLIN_HOME)/kremlib -I $(HACL_HOME)/code/hash

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

test-native-sha2_256.exe: sha2-c/Hacl_SHA2_256.o sha2-c/Hacl_Test_SHA2_256.o $(BASE_OBJ)
	$(CC) $(CFLAGS) -o $@ $^

test-native-sha2_384.exe: sha2-c/Hacl_SHA2_384.o sha2-c/Hacl_Test_SHA2_384.o $(BASE_OBJ)
	$(CC) $(CFLAGS) -o $@ $^

test-native-sha2_512.exe: sha2-c/Hacl_SHA2_512.o sha2-c/Hacl_Test_SHA2_512.o $(BASE_OBJ)
	$(CC) $(CFLAGS) -o $@ $^


clean:
	rm -rf *~ *.exe *.exe.dSYM
	rm -rf sha2-c sha2-*-c
