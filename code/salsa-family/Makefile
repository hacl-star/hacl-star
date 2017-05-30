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
	Spec.Chacha20_vec.fst \
	Spec.Chacha20_vec1.Lemmas.fst \
	Spec.CTR3.fst \
	Hacl.Impl.Chacha20.Vec128.State.fst \
	Hacl.Impl.Chacha20.Vec128.fst \
	Chacha20.Vec128.fst \
	Chacha20.Vec128.fsti

SLOW=

BROKEN=

FSTARB=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include $(HACL_HOME)/code/lib/kremlin --include $(KREMLIN_HOME)/kremlib \
		 --include $(HACL_HOME)/specs $(OTHERFLAGS)

FSTAR_CT=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include $(HACL_HOME)/code/lib --include $(KREMLIN_HOME)/kremlib \
		 --include $(HACL_HOME)/specs

KRML=$(KREMLIN_HOME)/krml -I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/specs \
	-drop FStar -drop Prims $(KREMLIN_HOME)/kremlib/testlib.c \
	-add-include '"testlib.h"' -drop 'Hacl.UInt8' $(KREMLIN_ARGS) \
	-drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
	-drop 'Hacl.Endianness' -drop 'Hacl.Cast'

# Lax typechecking against the restricted integer interface
%.fst-ct: %.fst
	$(FSTAR_CT) --lax $^
%.fsti-ct: %.fsti
	$(FSTAR_CT) --lax $^

# Using the --verify_all argument to lift abstractions, typechecks all dependencies of Curve25519.fst
all-ct:
	$(FSTAR_CT) --lax --verify_all Chacha20.fst Salsa20.fst Chacha20.Vec128.fst

# Full typechecking against the transparent integer interface
%.fst-verify: %.fst
	$(FSTARB) $^ --use_hints --record_hints
%.fsti-verify: %.fsti
	$(FSTARB) $^ --use_hints --record_hints

all-ver: $(addsuffix -verify, $(SALSA_FAMILY_FILES))

# For CI, all modules restricted from incomplete or slow ones
all-ci: $(addsuffix -verify, $(filter-out $(SLOW) $(BROKEN), $(SALSA_FAMILY_FILES)))

# Minimal lax typechecking, pre-requisite to any extraction
%.fst-lax: %.fst
	$(FSTARB) --lax $^
%.fsti-lax: %.fsti
	$(FSTARB) --lax $^

all-lax: $(addsuffix -lax, $(SALSA_FAMILY_FILES))

# Hints regeneration
%.fst-hints: %.fst
	-$(FSTARB) $^ --use_hints --record_hints
%.fsti-hints: %.fsti
	-$(FSTARB) $^ --use_hints --record_hints

all-hints: $(addsuffix -hints, $(filter-out $(BROKEN), $(SALSA_FAMILY_FILES)))

chacha-c/Chacha20.c: Hacl.Lib.LoadStore32.fst Hacl.Lib.Create.fst Hacl.Impl.Xor.Lemmas.fst Hacl.Impl.Chacha20.fst Chacha20.fst
	mkdir -p chacha-c
	$(KRML) -tmpdir chacha-c \
		-bundle 'Chacha20=Hacl.Impl.\*,Chacha20,Hacl.Lib.\*' \
		$(addprefix -drop , "C.Loops" "Hacl.Spec.\*" "Spec.\*" "Seq.\*") \
		Chacha20.fst $(VERBOSE) -skip-compilation

chacha20.exe: Hacl.Impl.Chacha20.fst Hacl.Test.Chacha20.fst Chacha20.fst
	mkdir -p chacha-c
	$(KRML) $(KREMLIN_ARGS) -tmpdir chacha-c  -no-prefix Hacl.Test.Chacha20 -I . \
		$(addprefix -drop , "C.Loops" "Hacl.Spec.\*" "Spec.\*" "Seq.\*") \
		-bundle 'Chacha20=Chacha20,Hacl.Impl.\*,Hacl.Lib.\*' \
		Chacha20.fst Hacl.Test.Chacha20.fst -o chacha20.exe
	./chacha20.exe

salsa-c/Salsa20.c: Hacl.Impl.Salsa20.fst Salsa20.fst
	mkdir -p salsa-c
	$(KRML) $(KREMLIN_ARGS) -tmpdir salsa-c -I . -skip-compilation \
		-bundle 'Salsa20=Salsa20,Hacl.Impl.\*,Hacl.Lib.\*' \
		$(addprefix -drop , "C.Loops" "Hacl.Spec.\*" "Spec.\*" "Seq.\*") \
		Salsa20.fst

salsa20.exe: Hacl.Impl.Salsa20.fst Salsa20.fst Hacl.Test.Salsa20.fst
	mkdir -p salsa-c
	$(KRML) $(KREMLIN_ARGS) -tmpdir salsa-c  -no-prefix Hacl.Test.Salsa20 \
		-bundle 'Salsa20=Salsa20,Hacl.Impl.\*,Hacl.Lib.\*' \
		$(addprefix -drop , "C.Loops" "Hacl.Spec.\*" "Spec.\*" "Seq.\*") \
		$^ -o salsa20.exe
	./salsa20.exe

chacha-vec128/Chacha20_Vec128.c: Hacl.Impl.Chacha20.Vec128.State.fst Hacl.Impl.Chacha20.Vec128.fst Chacha20.Vec128.fst
	mkdir -p chacha-vec128
	$(KRML) -tmpdir chacha-vec128 -no-prefix Hacl.UInt32x4 -I $(HACL_HOME)/specs -drop "Spec.\*,C.Loops,Hacl.Spec.\*,Seq.\*,Hacl.UInt32x4" -bundle "Chacha20.Vec128=Chacha20.Vec128,Hacl.Impl.\*" \
	-add-include '"vec128.h"' -I . \
	$^ -skip-compilation

extract-c: chacha-c/Chacha20.c salsa-c/Salsa20.c chacha-vec128/Chacha20_Vec128.c

clean:
	rm -rf *.exe *.exe.* *.out *~ salsa-c chacha-c chacha-vec128 *.graph
