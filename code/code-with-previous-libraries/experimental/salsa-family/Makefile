include ../../../Makefile.include

FSTARB=$(FSTAR_HOME)/bin/fstar.exe \
		--include $(HACL_HOME)/code/lib/kremlin --include $(KREMLIN_HOME)/kremlib/compat \
		 --include $(HACL_HOME)/specs --include $(HACL_HOME)/specs/experimental \
		--include $(HACL_HOME)/code/salsa-family

FSTAR_CT=$(FSTAR_HOME)/bin/fstar.exe \
		--include $(HACL_HOME)/code/lib --include $(KREMLIN_HOME)/kremlib/compat \
		 --include $(HACL_HOME)/specs --include $(HACL_HOME)/specs/experimental \
		--include $(HACL_HOME)/code/salsa-family

CHACHA_VEC_FILES=Hacl.Impl.Chacha20.Vec128.State.fst \
	Hacl.Impl.Chacha20.Vec128.fst \
	Chacha20.Vec128.fst \
	Chacha20.Vec128.fsti

# Lax typechecking against the restricted integer interface
%.fst-ct: %.fst
	$(FSTAR_CT) --lax $^
%.fsti-ct: %.fsti
	$(FSTAR_CT) --lax $^

# Full typechecking against the transparent integer interface
%.fst-verify: %.fst
	$(FSTARB) $^ --use_hints --record_hints
%.fsti-verify: %.fsti
	$(FSTARB) $^ --use_hints --record_hints

# Minimal lax typechecking, pre-requisite to any extraction
%.fst-lax: %.fst
	$(FSTARB) --lax $^

# Hints regeneration
%.fst-hints: %.fst
	-$(FSTARB) $^ --use_hints --record_hints

all-ver: $(addsuffix -verify, $(CHACHA_VEC_FILES))

all-ci: $(addsuffix -verify, $(CHACHA_VEC_FILES))

all-ct: $(addsuffix -ct, $(CHACHA_VEC_FILES))

SPECS_DIRS=$(HACL_HOME)/specs $(HACL_HOME)/specs/experimental

KRML=$(KREMLIN_HOME)/krml -I $(HACL_HOME)/code/lib/kremlin $(addprefix -I , $(SPECS_DIRS) $(HACL_HOME)/code/salsa-family) -drop FStar -drop Prims $(KREMLIN_HOME)/kremlib/c/testlib.c \
	-add-include '"testlib.h"' -drop 'Hacl.UInt8' $(KREMLIN_ARGS) \
	-drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
	-drop 'Hacl.Endianness' -drop 'Hacl.Cast'

Chacha20_vec.c: Hacl.UInt32x4N.fst Loops_vec.fst interfaces/Spec.Chacha20_vec256.fst Hacl.Impl.Chacha20_vec.fst Chacha20_vec.fst
	mkdir -p chacha-vec-c
	$(KRML) -tmpdir chacha-vec-c -no-prefix Loops_vec -no-prefix Hacl.UInt32x4N -I . -drop "Loops_vec" -drop "Hacl.UInt32x4N" \
		-bundle 'Chacha20_vec=Loops_vec,Hacl.Impl.Chacha20_state,Hacl.Impl.Chacha20_vec,Chacha20_vec' -drop 'Hacl.Spec.\*' -add-include '"loops_vec.h"' -drop 'Spec.\*' -drop "C.Loops" -add-include '"vec32x4N.h"' \
		$^ $(VERBOSE) -skip-linking

chacha-vec128/Chacha20_Vec128.c: Hacl.Impl.Chacha20.Vec128.State.fst Hacl.Impl.Chacha20.Vec128.fst Chacha20.Vec128.fst
	mkdir -p chacha-vec128
	$(KRML) -tmpdir chacha-vec128 -no-prefix Hacl.UInt32x4 -I $(HACL_HOME)/specs -drop "Spec.\*,C.Loops,Hacl.Spec.\*,Seq.\*,Hacl.UInt32x4" -bundle "Chacha20.Vec128=Chacha20.Vec128,Hacl.Impl.\*" \
	-add-include '"vec128.h"' -I . \
	$^ -skip-compilation

chacha20_vec128.exe: chacha-vec128/Chacha20_Vec128.c Hacl.Test.Chacha20.Vec128.fst
	$(KRML) -tmpdir chacha-vec128 \
	-add-include '"vec128.h"' -I . -drop 'Spec.\*,Seq.\*,Chacha20.Vec128' -add-include '"Chacha20_Vec128.h"' \
	-no-prefix Hacl.Test.Chacha20.Vec128 $^ -o chacha20_vec128.exe
	./chacha20_vec128.exe

Chacha20_vec2.c: interfaces/Hacl.UInt32x4N.fst Loops_vec.fst Hacl.Impl.Chacha20_vec2.fst Chacha20_vec2.fst
	mkdir -p chacha-vec2-c
	$(KRML) -tmpdir chacha-vec2-c -no-prefix Loops_vec -no-prefix Hacl.UInt32x4N -I . -drop "Loops_vec" -drop "Hacl.UInt32x4N" \
		-bundle 'Chacha20_vec2=Loops_vec,Hacl.Impl.Chacha20_state2,Hacl.Impl.Chacha20_vec2,Chacha20_vec2' -drop 'Hacl.Spec.\*' -add-include '"loops_vec.h"' -drop 'Spec.\*' -drop "C.Loops" -add-include '"vec32x4N.h"' \
		$^ $(VERBOSE) -skip-linking

extract-c: chacha-vec128/Chacha20_Vec128.c

count-line:
	cloc --force-lang=ocaml $(CHACHA_VEC_FILES)

clean:
	rm -rf *.exe *.exe.* *.out *~ chacha-vec-c chacha-vec2-c chacha-vec128
