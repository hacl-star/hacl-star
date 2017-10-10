include ../../Makefile.include

SALSA_FAMILY_FILES= \
	Hacl.Lib.LoadStore32.fst \
	Hacl.Lib.Create.fst \
	Hacl.Impl.Xor.Lemmas.fst \
	Hacl.Impl.Chacha20.fst \
	Hacl.Impl.Salsa20.fst \
	Hacl.Impl.HSalsa20.fst \
	Hacl.SecureAPI.Chacha20.fst \
	Chacha20.fst \
	Salsa20.fst \
	Spec.Chacha20_vec1.Lemmas.fst \
	Spec.CTR3.fst \
	Hacl.Impl.Chacha20.Vec128.State.fst \
	Hacl.Impl.Chacha20.Vec128.fst \
	Chacha20.Vec128.fst \
	Chacha20.Vec128.fsti

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
	$(FSTAR) --lax --verify_all Chacha20.fst Salsa20.fst Chacha20.Vec128.fst
verify: $(addsuffix -verify, $(SALSA_FAMILY_FILES))
hints: $(addsuffix .hints, $(filter-out $(BROKEN), $(SALSA_FAMILY_FILES)))

all-ci: ci
all-ct: ct
all-hints: hints
all-ver: verify

KREMLIN_ARGS+= \
	-drop Prims,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128,Hacl.Endianness,Hacl.Cast,Hacl.Spec.*,Spec.*,Seq.* \
	$(KREMLIN_TESTLIB)


chacha-c/out.krml: Hacl.Lib.LoadStore32.fst Hacl.Lib.Create.fst Hacl.Impl.Xor.Lemmas.fst Hacl.Impl.Chacha20.fst Chacha20.fst Hacl.Test.Chacha20.fst
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha-c \
		-bundle 'Chacha20=Hacl.Impl.*,Chacha20,Hacl.Lib.*' \
		-skip-translation $^ -o $@

chacha-c/Chacha20.c: chacha-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha-c \
		-bundle 'Chacha20=Hacl.Impl.*,Chacha20,Hacl.Lib.*' \
		-skip-compilation $^ -o $@

chacha20.exe: chacha-c/out.krml
	mkdir -p chacha-c
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha-c  -no-prefix Hacl.Test.Chacha20 \
		-bundle 'Chacha20=Chacha20,Hacl.Impl.*,Hacl.Lib.*' \
		$^ -o $@
	./$@


salsa-c/out.krml: Hacl.Impl.Salsa20.fst Salsa20.fst Hacl.Test.Salsa20.fst
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir salsa-c -skip-translation \
		-bundle 'Salsa20=Salsa20,Hacl.Impl.*,Hacl.Lib.*' \
		$^ -o $@

salsa-c/Salsa20.c: salsa-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir salsa-c -skip-compilation \
		-bundle 'Salsa20=Salsa20,Hacl.Impl.*,Hacl.Lib.*' \
		$^ -o $@

salsa20.exe: salsa-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir salsa-c  -no-prefix Hacl.Test.Salsa20 \
		-bundle 'Salsa20=Salsa20,Hacl.Impl.*,Hacl.Lib.*' \
		$^ -o $@
	./$@


chacha-vec128-c/out.krml: Hacl.Impl.Chacha20.Vec128.State.fst Hacl.Impl.Chacha20.Vec128.fst Chacha20.Vec128.fst Hacl.Test.Chacha20.Vec128.fst
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha-vec128-c \
		-bundle "Chacha20.Vec128=Chacha20.Vec128,Hacl.Impl.*,Hacl.Lib.*" \
		-add-include '"vec128.h"' \
		-skip-translation $^ -o $@

chacha-vec128-c/Chacha20_Vec128.c: chacha-vec128-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha-vec128-c \
		-no-prefix Hacl.UInt32x4 -add-include '"vec128.h"' -drop Hacl.UInt32x4 \
		-bundle "Chacha20.Vec128=Chacha20.Vec128,Hacl.Impl.*,Hacl.Lib.*" \
		-skip-compilation $^ -o $@

chacha20-vec128.exe: chacha-vec128-c/out.krml
	# Wintersteigr: Fix me; there is no Hacl.Test.Chacha20.Vec128 yet.
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha-vec128-c -no-prefix Hacl.Test.Chacha20.Vec128 \
		-no-prefix Hacl.UInt32x4 -add-include '"vec128.h"' -drop Hacl.UInt32x4 \
		-bundle "Chacha20.Vec128=Chacha20.Vec128,Hacl.Impl.*,Hacl.Lib.*" \
		$^ -o $@
	./$@

extract-c: chacha-c/Chacha20.c salsa-c/Salsa20.c chacha-vec128-c/Chacha20_Vec128.c

test: chacha20.exe salsa20.exe chacha20-vec128.exe

clean:
	rm -rf *.exe *.exe.* *.out *~ salsa-c chacha-c chacha-vec128-c *.graph
