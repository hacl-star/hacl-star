FSTAR_HOME?=../../../dependencies/FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
HACL_HOME?=../..
include ../Makefile.include


SALSA_FILES= \
	Hacl.Test.Chacha20.fst \
	Hacl.Test.Salsa20.fst \
	Hacl.Test.XSalsa20.fst 

SALSA_FAMILY_FILES= \
	Hacl.Impl.Chacha20.fst \
	Hacl.Symmetric.Salsa20.fst \
	Hacl.Impl.Salsa20.fst \
	Hacl.Symmetric.HSalsa20.fst \
	Hacl.Symmetric.XSalsa20.fst \
	Chacha20.fst \
	Salsa20.fst


SALSA_MODULES= $(basename $(SALSA_FILES))

SLOW=Hacl.Symmetric.Salsa20.fst \


FSTARB=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib/kremlin --include ../bignum --include $(KREMLIN_HOME)/kremlib \
		 --include ../../specs --include ../../specs/generic --include ../../specs/experimental

FSTAR_CT=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib --include ../bignum --include $(KREMLIN_HOME)/kremlib \
		 --include ../../specs --include ../../specs/generic --include ../../specs/experimental

# Lax typechecking against the restricted integer interface
%.fst-ct: %.fst
	$(FSTAR_CT) --lax $^

all-ct: $(addsuffix -ct, $(SALSA_FAMILY_FILES))

# Full typechecking against the transparent integer interface
%.fst-verify: %.fst
	-$(FSTARB) $^ --use_hints --record_hints

all-ver: $(addsuffix -verify, $(SALSA_FAMILY_FILES))

# For CI, all modules restricted from incomplete or slow ones
all-ci: $(addsuffix -verify, $(filter-out $(SLOW), $(SALSA_FAMILY_FILES)))

# Minimal lax typechecking, pre-requisite to any extraction
%.fst-lax: %.fst
	$(FSTARB) --lax $^

all-lax: $(addsuffix -lax, $(SALSA_FAMILY_FILES))

# Hints regeneration
%.fst-hints: %.fst
	-$(FSTARB) $^ --use_hints --record_hints

all-hints: $(addsuffix -hints, $(SALSA_FAMILY_FILES))

KRML=$(KREMLIN_HOME)/krml -I ../lib/kremlin -I ../../specs -I ../../specs/experimental -I ../../specs/generic -drop FStar -drop Prims $(KREMLIN_HOME)/kremlib/testlib.c \
	-add-include '"testlib.h"' -ccopt -march=native -ccopt -std=gnu99 -drop 'Hacl.UInt8' \
	-drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
	-drop 'Hacl.Endianness' -drop 'Hacl.Cast'

Chacha20.compcert: Hacl.Symmetric.Chacha20.fst Hacl.Test.Chacha20.fst Chacha20.fst
	mkdir -p chacha-cc
	$(KREMLIN_HOME)/krml -tmpdir chacha-cc \
		-I ../bignum -I ../lib/kremlin \
		Hacl.Symmetric.Chacha20.fst Hacl.Test.Chacha20.fst -o chacha20cc.exe -no-prefix Hacl.Test.Chacha20 \
		-drop 'Hacl.Spec.\*' -drop 'Hacl.Spe.\*' -drop 'Hacl.Cast' -drop 'Hacl.UInt.\*' \
		-drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
		-drop Prims -drop FStar \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -cc compcert
	./chacha20cc.exe

Chacha20.c: Hacl.Impl.Chacha20.fst Chacha20.fst
	mkdir -p chacha-c
	$(KRML) -tmpdir chacha-c -no-prefix Loops -I . -drop "Loops" \
		-bundle 'Chacha20=Hacl.Impl.Chacha20,Chacha20' -drop 'Hacl.Spec.\*' -add-include '"loops.h"' -drop 'Spec.\*' -drop "Combinators" \
		Chacha20.fst $(VERBOSE) -skip-linking

Chacha20_vec.c: Hacl.UInt32x4.fst Hacl.UInt32x8.fst Loops_vec.fst Hacl.Impl.Chacha20_vec.fst Chacha20_vec.fst
	mkdir -p chacha-c
	$(KRML) -tmpdir chacha-vec-c -no-prefix Loops_vec -no-prefix Hacl.UInt32x4 -no-prefix Hacl.UInt32x8 -I . -drop "Loops_vec" -drop "Hacl.UInt32x4" -drop "Hacl.UInt32x8" \
		-bundle 'Chacha20_vec=Loops_vec,Hacl.Impl.Chacha20_state,Hacl.Impl.Chacha20_vec,Chacha20_vec' -drop 'Hacl.Spec.\*' -add-include '"loops_vec.h"' -drop 'Spec.\*' -drop "Combinators" -add-include '"vec256.h"' \
		Chacha20_vec.fst $(VERBOSE) -skip-linking

chacha20.exe: Hacl.Impl.Chacha20.fst Hacl.Test.Chacha20.fst Chacha20.fst
	mkdir -p chacha-c
	$(KRML) -tmpdir chacha-c  -no-prefix Hacl.Test.Chacha20 -no-prefix Loops -I . -drop "Loops" \
		-bundle 'Chacha20=Chacha20,Hacl.Impl.Chacha20' -drop 'Hacl.Spec.\*' -add-include '"loops.h"' -drop 'Spec.\*' -drop "Combinators" \
		Chacha20.fst Hacl.Test.Chacha20.fst -o chacha20.exe $(VERBOSE)
	./chacha20.exe


Salsa.c: Hacl.Impl.Chacha20.fst
	mkdir -p salsa2-c
	$(KRML) -tmpdir salsa2-c  -no-prefix Hacl.Test2.Salsa20 -no-prefix Loops -I . -drop "Loops" \
		-bundle 'Salsa=Salsa,Hacl.Impl.Salsa20' -drop 'Hacl.Spec.\*' -add-include '"loops.h"' -drop 'Spec.\*' -drop "Combinators" \
		Hacl.Test2.Salsa20.fst -o salsa.exe $(VERBOSE)
	./salsa.exe

Salsa20.c: Hacl.Symmetric.Salsa20.fst Hacl.Test.Salsa20.fst
	mkdir -p salsa-c
	$(KRML) -tmpdir salsa-c $(VERBOSE) \
		Salsa20.fst Hacl.Test.Salsa20.fst -o salsa20.exe -no-prefix Hacl.Test.Salsa20 \
		-drop 'Hacl.Spec.\*' -drop 'Hacl.Spe.\*' -drop 'Hacl.UInt.\*' \
		-bundle Salsa20=Hacl.Symmetric.Salsa20
	./salsa20.exe

HSalsa20.c: Hacl.Symmetric.HSalsa20.fst 
	mkdir -p hsalsa-c
	$(KREMLIN_HOME)/krml -tmpdir hsalsa-c \
		-I ../bignum -I ../lib/kremlin \
		Hacl.Symmetric.HSalsa20.fst \
		-drop 'Hacl.Spec.\*' -drop 'Hacl.Spe.\*' -drop 'Hacl.Cast' -drop 'Hacl.UInt.\*' \
		-drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
		-drop Prims -drop FStar \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -skip-compilation  -ccopt -std=gnu99

XSalsa20.c: Hacl.Symmetric.XSalsa20.fst Hacl.Test.XSalsa20.fst
	mkdir -p xsalsa-c
	$(KRML) -tmpdir xsalsa-c \
		Hacl.Symmetric.XSalsa20.fst Hacl.Test.XSalsa20.fst -o xsalsa20.exe -no-prefix Hacl.Test.XSalsa20 \
		-drop 'Hacl.Spec.\*' -drop 'Hacl.Spe.\*' -drop 'Hacl.UInt.\*'
	./xsalsa20.exe

extract-c: Chacha20.c Salsa20.c HSalsa20.c XSalsa20.c Salsa.c


clean:
	rm -rf *.exe *.exe.* *.out *~ salsa-c salsa2-c chacha-c chacha-cc hsalsa-c xsalsa-c chacha2-c *.graph
