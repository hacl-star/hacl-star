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
		 --include ../../specs

FSTAR_CT=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib --include ../bignum --include $(KREMLIN_HOME)/kremlib \
		 --include ../../specs

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

KRML=$(KREMLIN_HOME)/krml -I ../lib/kremlin -I ../../specs -I ../../specs/experimental -drop FStar -drop Prims $(KREMLIN_HOME)/kremlib/testlib.c \
	-add-include '"testlib.h"' -drop 'Hacl.UInt8' $(KREMLIN_ARGS) \
	-drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
	-drop 'Hacl.Endianness' -drop 'Hacl.Cast'

Chacha20.c: Hacl.Impl.Chacha20.fst Chacha20.fst
	mkdir -p chacha-c
	$(KRML) -tmpdir chacha-c \
		-bundle 'Chacha20=Hacl.Impl.Chacha20,Chacha20' -drop 'Hacl.Spec.\*' -drop 'Spec.\*' -drop "C.Loops" \
		Chacha20.fst $(VERBOSE) -skip-linking

chacha20.exe: Hacl.Impl.Chacha20.fst Hacl.Test.Chacha20.fst Chacha20.fst
	mkdir -p chacha-c
	$(KRML) $(KREMLIN_ARGS) -tmpdir chacha-c  -no-prefix Hacl.Test.Chacha20 -I . -drop "C.Loops" \
		-bundle 'Chacha20=Chacha20,Hacl.Impl.Chacha20' -drop 'Hacl.Spec.\*' -drop 'Spec.\*'  \
		Chacha20.fst Hacl.Test.Chacha20.fst -o chacha20.exe
	./chacha20.exe


Salsa20.c: Hacl.Impl.Salsa20.fst Salsa20.fst
	mkdir -p salsa-c
	$(KRML) $(KREMLIN_ARGS) -tmpdir salsa-c -I . -skip-compilation \
		-bundle 'Salsa20=Salsa20,Hacl.Impl.Salsa20' -drop 'Hacl.Spec.\*' -drop 'Spec.\*' -drop "C.Loops" \
		$^

salsa20.exe: Hacl.Impl.Salsa20.fst Salsa20.fst Hacl.Test.Salsa20.fst
	mkdir -p salsa-c
	$(KRML) $(KREMLIN_ARGS) -tmpdir salsa-c  -no-prefix Hacl.Test.Salsa20 \
		-bundle 'Salsa20=Salsa20,Hacl.Impl.Salsa20' -drop 'Hacl.Spec.\*' -drop 'Spec.\*' -drop "C.Loops" \
		$^ -o salsa20.exe
	./salsa20.exe

HSalsa20.c: Hacl.Symmetric.HSalsa20.fst 
	mkdir -p hsalsa-c
	$(KREMLIN_HOME)/krml $(KREMLIN_ARGS) -tmpdir hsalsa-c \
		-I ../bignum -I ../lib/kremlin \
		Hacl.Symmetric.HSalsa20.fst \
		-drop 'Hacl.Spec.\*' -drop 'Hacl.Spe.\*' -drop 'Hacl.Cast' -drop 'Hacl.UInt.\*' \
		-drop 'Hacl.UInt8' -drop 'Hacl.UInt16' -drop 'Hacl.UInt32' -drop 'Hacl.UInt64' -drop 'Hacl.UInt128' \
		-drop Prims -drop FStar \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -skip-compilation  -ccopt -std=gnu99

XSalsa20.c: Hacl.Symmetric.XSalsa20.fst Hacl.Test.XSalsa20.fst
	mkdir -p xsalsa-c
	$(KRML) $(KREMLIN_ARGS) -tmpdir xsalsa-c \
		Hacl.Symmetric.XSalsa20.fst Hacl.Test.XSalsa20.fst -o xsalsa20.exe -no-prefix Hacl.Test.XSalsa20 \
		-drop 'Hacl.Spec.\*' -drop 'Hacl.Spe.\*' -drop 'Hacl.UInt.\*'
	./xsalsa20.exe

extract-c: Chacha20.c Salsa20.c HSalsa20.c XSalsa20.c


clean:
	rm -rf *.exe *.exe.* *.out *~ salsa-c chacha-c hsalsa-c xsalsa-c *.graph
