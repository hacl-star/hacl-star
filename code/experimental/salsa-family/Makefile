FSTAR_HOME?=../../../dependencies/FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
HACL_HOME?=../../..
include $(HACL_HOME)/code/Makefile.include

FSTARB=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib/kremlin --include ../bignum --include $(KREMLIN_HOME)/kremlib \
		 --include ../../specs --include ../../specs/generic --include ../../specs/experimental

FSTAR_CT=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib --include ../bignum --include $(KREMLIN_HOME)/kremlib \
		 --include ../../specs --include ../../specs/generic --include ../../specs/experimental

# Lax typechecking against the restricted integer interface
%.fst-ct: %.fst
	$(FSTAR_CT) --lax $^

# Full typechecking against the transparent integer interface
%.fst-verify: %.fst
	-$(FSTARB) $^ --use_hints --record_hints

# Minimal lax typechecking, pre-requisite to any extraction
%.fst-lax: %.fst
	$(FSTARB) --lax $^

# Hints regeneration
%.fst-hints: %.fst
	-$(FSTARB) $^ --use_hints --record_hints

SPECS_DIRS=$(HACL_HOME)/specs $(HACL_HOME)/specs/generic $(HACL_HOME)/specs/experimental

KRML=$(KREMLIN_HOME)/krml -I $(HACL_HOME)/code/lib/kremlin $(addprefix -I , $(SPECS_DIRS)) -drop FStar -drop Prims $(KREMLIN_HOME)/kremlib/testlib.c \
	-add-include '"testlib.h"' -drop 'Hacl.UInt8' $(KREMLIN_ARGS) \
	-drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
	-drop 'Hacl.Endianness' -drop 'Hacl.Cast'

Chacha20_vec.c: Hacl.UInt32x4N.fst Loops_vec.fst interfaces/Spec.Chacha20_vec256.fst Hacl.Impl.Chacha20_vec.fst Chacha20_vec.fst
	mkdir -p chacha-vec-c
	$(KRML) -tmpdir chacha-vec-c -no-prefix Loops_vec -no-prefix Hacl.UInt32x4N -I . -drop "Loops_vec" -drop "Hacl.UInt32x4N" \
		-bundle 'Chacha20_vec=Loops_vec,Hacl.Impl.Chacha20_state,Hacl.Impl.Chacha20_vec,Chacha20_vec' -drop 'Hacl.Spec.\*' -add-include '"loops_vec.h"' -drop 'Spec.\*' -drop "C.Loops" -add-include '"vec32x4N.h"' \
		$^ $(VERBOSE) -skip-linking

Chacha20_vec2.c: interfaces/Hacl.UInt32x4N.fst Loops_vec.fst Hacl.Impl.Chacha20_vec2.fst Chacha20_vec2.fst
	mkdir -p chacha-vec2-c
	$(KRML) -tmpdir chacha-vec2-c -no-prefix Loops_vec -no-prefix Hacl.UInt32x4N -I . -drop "Loops_vec" -drop "Hacl.UInt32x4N" \
		-bundle 'Chacha20_vec2=Loops_vec,Hacl.Impl.Chacha20_state2,Hacl.Impl.Chacha20_vec2,Chacha20_vec2' -drop 'Hacl.Spec.\*' -add-include '"loops_vec.h"' -drop 'Spec.\*' -drop "C.Loops" -add-include '"vec32x4N.h"' \
		$^ $(VERBOSE) -skip-linking

extract-c: Chacha20_vec.c Chacha20_vec2.c


clean:
	rm -rf *.exe *.exe.* *.out *~ chacha-vec-c chacha-vec2-c
