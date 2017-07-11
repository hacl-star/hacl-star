include ../Makefile.include

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
	-drop FStar,Prims,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128,Hacl.Endianness,Hacl.Cast,Hacl.Spec.*,Spec.*,Seq.* \
	$(KREMLIN_TESTLIB)

chacha-c/Chacha20.c: Hacl.Lib.LoadStore32.fst Hacl.Lib.Create.fst Hacl.Impl.Xor.Lemmas.fst Hacl.Impl.Chacha20.fst Chacha20.fst
	mkdir -p chacha-c
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha-c \
		-bundle 'Chacha20=Hacl.Impl.\*,Chacha20,Hacl.Lib.\*' \
		Chacha20.fst $(VERBOSE) -skip-compilation

chacha20.exe: Hacl.Impl.Chacha20.fst Chacha20.fst Hacl.Test.Chacha20.fst
	mkdir -p chacha-c
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha-c  -no-prefix Hacl.Test.Chacha20 \
		-bundle 'Chacha20=Chacha20,Hacl.Impl.\*,Hacl.Lib.\*' \
		$^ -o $@
	./$@

salsa-c/Salsa20.c: Hacl.Impl.Salsa20.fst Salsa20.fst
	mkdir -p salsa-c
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir salsa-c -skip-compilation \
		-bundle 'Salsa20=Salsa20,Hacl.Impl.\*,Hacl.Lib.\*' \
		Salsa20.fst

salsa20.exe: Hacl.Impl.Salsa20.fst Salsa20.fst Hacl.Test.Salsa20.fst
	mkdir -p salsa-c
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir salsa-c  -no-prefix Hacl.Test.Salsa20 \
		-bundle 'Salsa20=Salsa20,Hacl.Impl.\*,Hacl.Lib.\*' \
		$^ -o $@
	./$@

chacha20-vec128/Chacha20_Vec128.c: Hacl.Impl.Chacha20.Vec128.State.fst Hacl.Impl.Chacha20.Vec128.fst Chacha20.Vec128.fst
	mkdir -p chacha20-vec128
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha20-vec128 -no-prefix Hacl.UInt32x4 -I $(HACL_HOME)/specs -drop "Hacl.UInt32x4" \
	-bundle "Chacha20.Vec128=Chacha20.Vec128,Hacl.Impl.\*" \
	-add-include '"vec128.h"' \
	$^ -skip-compilation

extract-c: chacha-c/Chacha20.c salsa-c/Salsa20.c chacha20-vec128/Chacha20_Vec128.c

test: chacha20.exe salsa20.exe

clean:
	rm -rf *.exe *.exe.* *.out *~ salsa-c chacha-c chacha-vec128 *.graph
