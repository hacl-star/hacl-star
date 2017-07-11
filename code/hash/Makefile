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

# Extraction
extract-c: sha2-256-c/SHA2_256.c sha2-384-c/SHA2_384.c sha2-512-c/SHA2_512.c

test: test-sha2_256.exe test-sha2_384.exe test-sha2_512.exe


sha2-c/out.krml: $(SHA2_FILES)
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir sha2-c $^

sha2-256-c/SHA2_256.c sha2-256-c/Hacl_Test_SHA2_256.c: sha2-c/out.krml SHA2_256.fst 
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir sha2-256-c -skip-compilation -no-prefix Hacl.Test.SHA2_256 \
		-drop SHA2_384,SHA2_512,Hacl.Hash.SHA2_384,Hacl.Hash.SHA2_512 \
		-bundle "SHA2_256=Hacl.Hash.Lib.Create,Hacl.Hash.Lib.LoadStore,Hacl.Hash.SHA2_256,SHA2_256" \
		$^ -o $@

sha2-384-c/SHA2_384.c sha2-384-c/Hacl_Test_SHA2_384.c: sha2-c/out.krml SHA2_384.fst 
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir sha2-384-c -skip-compilation -no-prefix Hacl.Test.SHA2_384 \
		-drop SHA2_256,SHA2_512,Hacl.Hash.SHA2_256,Hacl.Hash.SHA2_512 \
		-bundle "SHA2_384=Hacl.Hash.Lib.Create,Hacl.Hash.Lib.LoadStore,Hacl.Hash.SHA2_384,SHA2_384" \
		$^ -o $@

sha2-512-c/SHA2_512.c sha2-512-c/Hacl_Test_SHA2_512.c: sha2-c/out.krml SHA2_512.fst
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir sha2-512-c -skip-compilation -no-prefix Hacl.Test.SHA2_512 \
		-drop SHA2_384,SHA2_256,Hacl.Hash.SHA2_384,Hacl.Hash.SHA2_256 \
		-bundle "SHA2_512=Hacl.Hash.Lib.Create,Hacl.Hash.Lib.LoadStore,Hacl.Hash.SHA2_512,SHA2_512" \
		$^ -o $@

test-sha2_256.exe: SHA2_256.fst Hacl.Test.SHA2_256.fst 
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir sha2-256-c -no-prefix Hacl.Test.SHA2_256 \
		-drop SHA2_384,SHA2_512,Hacl.Hash.SHA2_384,Hacl.Hash.SHA2_512 \
		-bundle "SHA2_256=Hacl.Hash.Lib.Create,Hacl.Hash.Lib.LoadStore,Hacl.Hash.SHA2_256,SHA2_256" \
		$^ -o $@
	./$@

test-sha2_384.exe: SHA2_384.fst Hacl.Test.SHA2_384.fst 
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir sha2-384-c -no-prefix Hacl.Test.SHA2_384 \
		-drop SHA2_256,SHA2_512,Hacl.Hash.SHA2_256,Hacl.Hash.SHA2_512 \
		-bundle "SHA2_384=Hacl.Hash.Lib.Create,Hacl.Hash.Lib.LoadStore,Hacl.Hash.SHA2_384,SHA2_384" \
		$^ -o $@
	./$@

test-sha2_512.exe: SHA2_512.fst Hacl.Test.SHA2_512.fst 
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir sha2-512-c -no-prefix Hacl.Test.SHA2_512 \
		-drop SHA2_384,SHA2_256,Hacl.Hash.SHA2_384,Hacl.Hash.SHA2_256 \
		-bundle "SHA2_512=Hacl.Hash.Lib.Create,Hacl.Hash.Lib.LoadStore,Hacl.Hash.SHA2_512,SHA2_512" \
		$^ -o $@
	./$@


# The following 'native' test targets use CC and CFLAGS, which may be different from the compiler and 
# flags that Kremlin uses/chooses. So, use with care.

test-native: test-native-sha2_256.exe test-native-sha2_384.exe test-native-sha2_512.exe

BASE_OBJ=$(VALE_A) sha2-c/testlib.o sha2-c/kremlib.o

$(BASE_OBJ): sha2-c/out.krml

CFLAGS=-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/specs -I $(KREMLIN_HOME)/kremlib -I $(HACL_HOME)/code/hash

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

test-native-sha2_256.exe: sha2-256-c/SHA2_256.o sha2-256-c/Hacl_Test_SHA2_256.o $(BASE_OBJ)
	$(CC) $(CFLAGS) -o $@ $^

test-native-sha2_384.exe: sha2-384-c/SHA2_384.o sha2-384-c/Hacl_Test_SHA2_384.o $(BASE_OBJ)
	$(CC) $(CFLAGS) -o $@ $^

test-native-sha2_512.exe: sha2-512-c/SHA2_512.o sha2-512-c/Hacl_Test_SHA2_512.o $(BASE_OBJ)
	$(CC) $(CFLAGS) -o $@ $^



clean:
	rm -rf *~ *.exe *.exe.dSYM
	rm -rf sha2-c sha2-*-c
