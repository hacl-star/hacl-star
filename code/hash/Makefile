include ../Makefile.include

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

ct: $(addsuffix -lax, $(SHA2_FILES))
verify: $(addsuffix -verify, $(SHA2_FILES))
hints: $(addsuffix .hints, $(SHA2_FILES))
all-ct: ct
all-ver: verify
all-ci: verify
all-hints: hints


KREMLIN_ARGS+=-verbose \
	-drop Prims,FStar,Hacl.Cast,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128 \
	-drop Hacl.Spec.Endianness,Hacl.Endianness,Seq.Create,Spec.* \
	-drop Hacl.Hash.SHA2_256.Lemmas,Hacl.Hash.SHA2_384.Lemmas,Hacl.Hash.SHA2_512.Lemmas \
	$(KREMLIN_TESTLIB) -ccopt -march=native

extract-c: $(addprefix sha2-c/, $(foreach N,256 384 512, SHA2_$(N).c Hacl_Test_SHA2_$(N).c))

test: test-sha2_256.exe test-sha2_384.exe test-sha2_512.exe

SPACE=$(noop) $(noop)
MODULES=SHA2_256 SHA2_384 SHA2_512 Hacl.Hash.SHA2_256 Hacl.Hash.SHA2_384 Hacl.Hash.SHA2_512

sha2-c/SHA2_%.c: SHA2_%.fst 
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir sha2-c -skip-compilation -no-prefix Hacl.Test.SHA2_$* \
	-drop $(subst $(SPACE),,$(filter-out Hacl.Hash.SHA2_$*,$(filter-out SHA2_$*,$(MODULES)))) \
	-bundle "SHA2_$*=Hacl.Hash.Lib.Create,Hacl.Hash.Lib.LoadStore,Hacl.Hash.SHA2_$*,SHA2_$*" \
	$^ -o $@

sha2-c/Hacl_Test_SHA2_%.c: Hacl.Test.SHA2_%.fst
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir sha2-c -skip-compilation -no-prefix Hacl.Test.SHA2_$* \
	-drop $(subst $(SPACE),,$(filter-out Hacl.Hash.SHA2_$*,$(filter-out SHA2_$*,$(MODULES)))) \
	-bundle "SHA2_$*=Hacl.Hash.Lib.Create,Hacl.Hash.Lib.LoadStore,Hacl.Hash.SHA2_$*,SHA2_$*" \
	$^ -o $@

test-sha2_%.exe: SHA2_%.fst Hacl.Test.SHA2_%.fst 
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir sha2-$*-c -no-prefix Hacl.Test.SHA2_$* \
		-drop $(subst $(SPACE),,$(filter-out Hacl.Hash.SHA2_$*,$(filter-out SHA2_$*,$(MODULES)))) \
		-bundle "SHA2_$*=Hacl.Hash.Lib.Create,Hacl.Hash.Lib.LoadStore,Hacl.Hash.SHA2_$*,SHA2_$*" \
		$^ -o $@
	./$@


# The following 'native' test targets use CC and CFLAGS, which may be different from the compiler and 
# flags that Kremlin uses/chooses. So, use with care.

test-native: test-native-sha2_256.exe test-native-sha2_384.exe test-native-sha2_512.exe

sha2-c/out.krml: $(SHA2_FILES) SHA2_256.fst SHA2_384.fst SHA2_512.fst Hacl.Test.SHA2_256.fst Hacl.Test.SHA2_384.fst Hacl.Test.SHA2_512.fst
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir sha2-c -skip-translation $^

BASE_OBJ=$(VALE_A) sha2-c/testlib.o sha2-c/kremlib.o
$(BASE_OBJ): sha2-c/out.krml

CFLAGS=-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/specs -I $(KREMLIN_HOME)/kremlib -I $(HACL_HOME)/code/hash

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

test-native-sha2_256.exe: sha2-c/SHA2_256.o sha2-c/Hacl_Test_SHA2_256.o $(BASE_OBJ)
	$(CC) $(CFLAGS) -o $@ $^

test-native-sha2_384.exe: sha2-c/SHA2_384.o sha2-c/Hacl_Test_SHA2_384.o $(BASE_OBJ)
	$(CC) $(CFLAGS) -o $@ $^

test-native-sha2_512.exe: sha2-c/SHA2_512.o sha2-c/Hacl_Test_SHA2_512.o $(BASE_OBJ)
	$(CC) $(CFLAGS) -o $@ $^



clean:
	rm -rf *~ *.exe *.exe.dSYM
	rm -rf sha2-c sha2-*-c
