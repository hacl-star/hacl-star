include ../../Makefile.include

SALSA_FAMILY_FILES= \
	Hacl.Lib.LoadStore32.fst \
	Hacl.Lib.Create.fst \
	Hacl.Impl.Xor.Lemmas.fst \
	Hacl.Impl.Chacha20.fst \
	Hacl.Impl.Salsa20.fst \
	Hacl.Impl.HSalsa20.fst \
	Hacl.SecureAPI.Chacha20.fst \
	Hacl.Chacha20.fst \
	Hacl.Salsa20.fst \
	Spec.Chacha20_vec1.Lemmas.fst \
	Spec.CTR3.fst \
	Hacl.Impl.Chacha20.Vec128.State.fst \
	Hacl.Impl.Chacha20.Vec128.fst \
	Hacl.Chacha20.Vec128.fst \
	Hacl.Chacha20.Vec128.fsti

SLOW=

BROKEN=

# Parameter for interactive mode
%.fst-in:
	@echo $(OPTIONS) --hint_info \
	$(FSTAR_INCLUDES)

# For CI, all modules restricted from incomplete or slow ones
ci: $(addsuffix -verify, $(filter-out $(SLOW) $(BROKEN), $(SALSA_FAMILY_FILES)))
ct: $(addsuffix -lax, $(SALSA_FAMILY_FILES))
	# Using the --verify_all argument to lift abstractions, typechecks all dependencies of Curve25519.fst
	$(FSTAR) --lax --verify_all Hacl.Chacha20.fst Hacl.Salsa20.fst Hacl.Chacha20.Vec128.fst
verify: $(addsuffix -verify, $(SALSA_FAMILY_FILES))
hints: $(addsuffix .hints, $(filter-out $(BROKEN), $(SALSA_FAMILY_FILES)))

all-ci: ci
all-ct: ct
all-hints: hints
all-ver: verify

KREMLIN_ARGS+= \
	-drop Prims,FStar,LowStar,C.Loops.Spec.Loops \
	-drop Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128,Hacl.Endianness,Hacl.Cast,Hacl.Spec.*,Spec.*,Seq.* \
	$(KREMLIN_TESTLIB) -I $(HACL_HOME)/specs -I $(HACL_HOME)/lib


chacha-c/out.krml: Hacl.Lib.LoadStore32.fst Hacl.Lib.Create.fst Hacl.Impl.Xor.Lemmas.fst Hacl.Impl.Chacha20.fst Hacl.Chacha20.fst Hacl.Test.Chacha20.fst
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha-c \
		-skip-translation $^ -o $@

chacha-c/Hacl_Chacha20.c: chacha-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha-c \
		-add-include '"kremlib.h"' -minimal -bundle 'Hacl.Chacha20=*' \
		-skip-compilation $^ -o $@

chacha20-ml.exe: ../../lib/Lib.IntTypes.fst ../../lib/Lib.RawIntTypes.fst ../../lib/ml/Lib.Loops.fst ../../lib/Lib.Buffer.fst ../../lib/ml/Lib.Endian.fst ../../lib/Lib.IntBuf.LoadStore.fst Hacl.Impl.Chacha20.fst
	mkdir -p chacha20-ml
	$(FSTAR) --include ../../specs --include ../../lib --include ../../lib/ml --codegen OCaml --lax --odir chacha20-ml $^
	$(OCAMLOPT) -I chacha20-ml chacha20-ml/Lib_Loops.ml chacha20-ml/Hacl_Impl_Chacha20.ml


chacha20-c/out.krml: ../../lib/Lib.IntTypes.fst ../../lib/Lib.RawIntTypes.fst ../../lib/c/Lib.Loops.fst ../../lib/Lib.Buffer.fst  ../../lib/Lib.ByteBuffer.fst  Hacl.Impl.Chacha20.fst Hacl.Test.Chacha20.fst
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha20-c \
		-bundle 'Hacl.Impl.Chacha20=Hacl.Impl.*,Lib.*' \
		-skip-translation $^ -o $@

BASE_OBJ = ../../lib/c/Lib_Print.o $(KREMLIN_HOME)/kremlib/testlib.o $(KREMLIN_HOME)/kremlib/kremlib.o $(KREMLIN_HOME)/kremlib/kremstr.o

../../lib/c/Lib_Print.o: ../../lib/c/Lib_Print.c
	$(CC) -c $^ -o $@

chacha20-c.exe: ../../lib/c/Lib_Print.o chacha20-c/out.krml
	mkdir -p chacha20-c
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha20-c  -no-prefix Hacl.Test.Chacha20 \
		-bundle 'Hacl.Impl.Chacha20=Hacl.Impl.*,Lib.*' \
		-skip-linking $^
	$(CC) ../../lib/c/Lib_Print.o chacha20-c/*.o -o $@
	./$@



chacha20.exe: chacha-c/out.krml
	mkdir -p chacha-c
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha-c -no-prefix Hacl.Test.Chacha20 \
		-add-include '"kremlib.h"' -minimal -bundle 'Hacl.Test.Chacha20=*' \
		-library Hacl.Chacha20 \
		$^ -o $@
	./$@


salsa-c/out.krml: Hacl.Impl.Salsa20.fst Hacl.Salsa20.fst Hacl.Test.Salsa20.fst
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir salsa-c -skip-translation \
		$^ -o $@

salsa-c/Hacl_Salsa20.c: salsa-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir salsa-c -skip-compilation \
		-add-include '"kremlib.h"' -minimal -bundle 'Hacl.Salsa20=*' \
		$^ -o $@

salsa20.exe: salsa-c/Hacl_Salsa20.c salsa-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir salsa-c  -no-prefix Hacl.Test.Salsa20 \
		-add-include '"kremlib.h"' -minimal -bundle 'Hacl.Test.Salsa20=*' \
		-library Hacl.Salsa20 \
		$^ -o $@
	./$@


chacha-vec128-c/out.krml: Hacl.Impl.Chacha20.Vec128.State.fst Hacl.Impl.Chacha20.Vec128.fst Hacl.Chacha20.Vec128.fst Hacl.Test.Chacha20.Vec128.fst
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha-vec128-c \
	  	-drop Hacl.UInt32x4 \
		-add-include '"vec128.h"' \
		-skip-translation $^ -o $@

chacha-vec128-c/Hacl_Chacha20_Vec128.c: chacha-vec128-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha-vec128-c \
		-drop Hacl.UInt32x4 -add-include '"vec128.h"' \
		-add-include '"kremlib.h"' -minimal -bundle "Hacl.Chacha20.Vec128=*" \
		-skip-compilation $^ -o $@

chacha20-vec128.exe: chacha-vec128-c/Hacl_Chacha20_Vec128.c chacha-vec128-c/out.krml
	cp ../../snapshots/common/vec128.h .
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha-vec128-c -no-prefix Hacl.Test.Chacha20.Vec128 \
	  -drop Hacl.UInt32x4 -add-include '"vec128.h"' \
	  -minimal -add-include '"kremlib.h"' -bundle Hacl.Test.Chacha20.Vec128=* \
	  $^ -o $@
	./$@

extract-c: chacha-c/Hacl_Chacha20.c salsa-c/Hacl_Salsa20.c chacha-vec128-c/Hacl_Chacha20_Vec128.c

test: chacha20.exe salsa20.exe chacha20-vec128.exe

clean:
	rm -rf *.exe *.exe.* *.out *~ salsa-c chacha-c chacha-vec128-c *.graph
