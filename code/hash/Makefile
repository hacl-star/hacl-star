include ../../Makefile.include

# Files for verification
SHA2_FILES = \
	Hacl.Hash.Lib.LoadStore.fst \
	Hacl.Hash.Lib.Create.fst \
	Hacl.Impl.SHA2_512.Lemmas.fst \
	Hacl.Impl.SHA2_512.fst \
	Hacl.Impl.SHA2_384.Lemmas.fst \
	Hacl.Impl.SHA2_384.fst \
	Hacl.Impl.SHA2_256.Lemmas.fst \
	Hacl.Impl.SHA2_256.fst

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
	-drop Prims,Hacl.Cast,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128 \
	-drop Hacl.Spec.Endianness,Hacl.Endianness,Seq.Create,Spec.* \
	-drop Hacl.Impl.SHA2_256.Lemmas,Hacl.Impl.SHA2_384.Lemmas,Hacl.Impl.SHA2_512.Lemmas \
	$(KREMLIN_TESTLIB) -ccopt -march=native

MODULES=$(foreach N,256 384 512,Hacl.SHA2_$(N) Hacl.Impl.SHA2_$(N))
TESTMODS=$(foreach N,256 384 512,Hacl.Test.SHA2_$(N))

extract-c: $(addprefix sha2-c/, $(foreach N,256 384 512,Hacl_SHA2_$(N).c Hacl_Test_SHA2_$(N).c))
test: test-sha2_256.exe test-sha2_384.exe test-sha2_512.exe

SPACE=$(empty) $(empty)
COMMA=,

sha2-c/out.krml: $(SHA2_FILES) $(addsuffix .fst,$(MODULES)) $(addsuffix .fst,$(TESTMODS))
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir sha2-c -skip-translation $^

sha2-c/Hacl_SHA2_%.c: sha2-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir sha2-c -skip-compilation \
	 -drop $(subst $(SPACE),$(COMMA),$(filter-out Hacl.Impl.SHA2_$*,$(filter-out Hacl.SHA2_$*,$(MODULES)))) \
	-drop $(subst $(SPACE),$(COMMA),$(TESTMODS)) \
	 -bundle "Hacl.SHA2_$*=Hacl.Hash.Lib.Create,Hacl.Hash.Lib.LoadStore,Hacl.Impl.SHA2_$*,Hacl.SHA2_$*" \
	 $^ -o $@

sha2-c/Hacl_Test_SHA2_%.c: sha2-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir sha2-c -skip-compilation -no-prefix Hacl.Test.SHA2_$* \
	-drop $(subst $(SPACE),$(COMMA),$(filter-out Hacl.Impl.SHA2_$*,$(filter-out Hacl.SHA2_$*,$(MODULES)))) \
	-drop $(subst $(SPACE),$(COMMA),$(filter-out Hacl.Test.SHA2_$*,$(TESTMODS))) \
	-bundle "Hacl.SHA2_$*=Hacl.Hash.Lib.Create,Hacl.Hash.Lib.LoadStore,Hacl.Impl.SHA2_$*,Hacl.SHA2_$*" \
	$^ -o $@

test-sha2_%.exe: sha2-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir sha2-$*-c -no-prefix Hacl.Test.SHA2_$* \
	-drop $(subst $(SPACE),$(COMMA),$(filter-out Hacl.Impl.SHA2_$*,$(filter-out Hacl.SHA2_$*,$(MODULES)))) \
	-drop $(subst $(SPACE),$(COMMA),$(filter-out Hacl.Test.SHA2_$*,$(TESTMODS))) \
	-bundle "Hacl.SHA2_$*=Hacl.Hash.Lib.Create,Hacl.Hash.Lib.LoadStore,Hacl.Impl.SHA2_$*,Hacl.SHA2_$*" \
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

test-native-sha2_256.exe: sha2-c/Hacl_SHA2_256.o sha2-c/Hacl_Test_SHA2_256.o $(BASE_OBJ)
	$(CC) $(CFLAGS) -o $@ $^

test-native-sha2_384.exe: sha2-c/Hacl_SHA2_384.o sha2-c/Hacl_Test_SHA2_384.o $(BASE_OBJ)
	$(CC) $(CFLAGS) -o $@ $^

test-native-sha2_512.exe: sha2-c/Hacl_SHA2_512.o sha2-c/Hacl_Test_SHA2_512.o $(BASE_OBJ)
	$(CC) $(CFLAGS) -o $@ $^


# blake2s-c/out.krml: ../../specs/lib/fst/Spec.Lib.IntTypes.fst ../../specs/lib/fst/Spec.Lib.RawIntTypes.fst ../../specs/lib/c/Spec.Lib.Loops.fst ../../specs/lib/fst/Spec.Lib.IntBuf.fst  ../../specs/lib/c/Spec.Lib.Endian.fst ../../specs/lib/fst/Spec.Lib.IntBuf.LoadStore.fst Hacl.Impl.Blake2s.fst Hacl.Test.Blake2s.fst
# 	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir blake2s-c -drop Spec.* \
# 		-I ../../specs -I ../../specs/lib -I ../../specs/lib/fst \
# 		-bundle 'Hacl.Impl.Blake2s=Hacl.Impl.*,Spec.Lib.*' \
# 		-skip-translation $^ -o $@


# blake2s-c.exe: blake2s-c/out.krml
# 	mkdir -p blake2s-c
# 	$(KREMLIN) $(KREMLIN_ARGS) -drop Spec.* -tmpdir blake2s-c  -no-prefix Hacl.Test.Blake2s \
# 		-I ../../specs -I ../../specs/lib -I ../../specs/lib/fst -I ../../specs/lib/c \
# 		-bundle 'Hacl.Impl.Blake2s=Hacl.Impl.*,Spec.Lib.*' \
# 		$^ -o $@
# 	./$@


blake2s-c/out.krml: ../../specs/lib/fst/Spec.Lib.IntTypes.fst ../../specs/lib/fst/Spec.Lib.RawIntTypes.fst ../../specs/lib/c/Spec.Lib.Loops.fst ../../specs/lib/fst/Spec.Lib.IntBuf.fst  ../../specs/lib/c/Spec.Lib.Endian.fst ../../specs/lib/fst/Spec.Lib.IntBuf.LoadStore.fst Hacl.Impl.Blake2s.fst Hacl.Blake2s.fst Hacl.Test.Blake2s.fst
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir blake2s-c \
	-I ../../specs -I ../../specs/lib -I ../../specs/lib/fst \
	-skip-translation $^

blake2s-c/Hacl_Blake2s.c: blake2s-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir blake2s-c -no-prefix 'Hacl.Test.Blake2s' -skip-compilation \
	-bundle 'Hacl.Blake2s=Hacl.Impl.*,Hacl.Blake2s' \
	$^ -o $@

BASE_OBJ = $(KREMLIN_HOME)/kremlib/testlib.o $(KREMLIN_HOME)/kremlib/kremlib.o


test-blake2s.exe: blake2s-c/Hacl_Blake2s.o $(BASE_OBJ)
	$(CC) -I $(KREMLIN_HOME)/kremlib -o $@ blake2s-c/Hacl_Test_Blake2s.c $^
	./test-blake2s.exe

clean:
	rm -rf *~ *.exe *.exe.dSYM
	rm -rf sha2-c sha2-*-c
