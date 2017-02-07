FSTAR_HOME?=../../../dependencies/FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
HACL_HOME?=../..
include ../Makefile.include


SALSA_FILES= \
	Hacl.Test.Chacha20.fst \
	Hacl.Test.Salsa20.fst \
	Hacl.Test.XSalsa20.fst 
#	Hacl.Symmetric.Salsa20.fst \
	Hacl.Test.Chacha20_avx.fst \
	Hacl.Symmetric.HSalsa20.fst \
	Hacl.Symmetric.XSalsa20.fst \
	Hacl.Symmetric.Chacha20.fst \

SALSA_FAMILY_FILES= \
	Hacl.Symmetric.Chacha20.fst \
	Hacl.Symmetric.Salsa20.fst \
	Hacl.Symmetric.HSalsa20.fst \
	Hacl.Symmetric.XSalsa20.fst \


SALSA_MODULES= $(basename $(SALSA_FILES))


# Lax typechecking against the restricted integer interface
%.fst-ct: %.fst
	$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib --include ../bignum --lax $^

all-ct: $(addsuffix -ct, $(SALSA_FAMILY_FILES))

# Full typechecking against the transparent integer interface
%.fst-verify: %.fst
	-$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib/kremlin --include ../bignum $^ --use_hints

all-ver: $(addsuffix -verify, $(SALSA_FAMILY_FILES))

# Minimal lax typechecking, pre-requisite to any extraction
%.fst-lax: %.fst
	$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib/kremlin --include ../bignum --lax $^

all-lax: $(addsuffix -lax, $(SALSA_FAMILY_FILES))

# Hints regeneration
%.fst-hints: %.fst
	-$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib/kremlin --include ../bignum $^ --use_hints --record_hints

all-hints: $(addsuffix -hints, $(SALSA_FAMILY_FILES))


Chacha20.c: Hacl.Symmetric.Chacha20.fst Hacl.Test.Chacha20.fst Chacha20.fst
	mkdir -p salsa-c
	$(KREMLIN_HOME)/krml -tmpdir salsa-c -verbose \
		-I ../bignum -I ../lib/kremlin \
		Chacha20.fst Hacl.Test.Chacha20.fst -o chacha20.exe -no-prefix Hacl.Test.Chacha20 \
		-drop 'Hacl.Spec.\*' -drop 'Hacl.Spe.\*' -drop 'Hacl.Cast' -drop 'Hacl.UInt.\*' \
		-drop Prims -drop FStar -bundle Chacha20=Hacl.Symmetric.Chacha20 Chacha20.fst \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -ccopt -march=native -ccopt -std=gnu99 
	./chacha20.exe

Chacha20.compcert: Hacl.Symmetric.Chacha20.fst Hacl.Test.Chacha20.fst Chacha20.fst
	mkdir -p salsa-c
	$(KREMLIN_HOME)/krml -tmpdir salsa-c -verbose \
		-I ../bignum -I ../lib/kremlin \
		Hacl.Symmetric.Chacha20.fst Hacl.Test.Chacha20.fst -o chacha20.exe -no-prefix Hacl.Test.Chacha20 \
		-drop 'Hacl.Spec.\*' -drop 'Hacl.Spe.\*' -drop 'Hacl.Cast' -drop 'Hacl.UInt.\*' \
		-drop Prims -drop FStar \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -cc compcert
	./chacha20.exe

Salsa20.c: Hacl.Symmetric.Salsa20.fst Hacl.Test.Salsa20.fst
	mkdir -p salsa-c
	$(KREMLIN_HOME)/krml -tmpdir salsa-c -verbose \
		-I ../bignum -I ../lib/kremlin \
		Salsa20.fst Hacl.Test.Salsa20.fst -o salsa20.exe -no-prefix Hacl.Test.Salsa20 \
		-drop 'Hacl.Spec.\*' -drop 'Hacl.Spe.\*' -drop 'Hacl.Cast' -drop 'Hacl.UInt.\*' \
		-drop Prims -drop FStar  -bundle Salsa20=Hacl.Symmetric.Salsa20 \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -ldopt -flto -ccopt -march=native  -ccopt -std=gnu99
	./salsa20.exe

HSalsa20.c: Hacl.Symmetric.HSalsa20.fst 
	mkdir -p salsa-c
	$(KREMLIN_HOME)/krml -tmpdir salsa-c -verbose \
		-I ../bignum -I ../lib/kremlin \
		Hacl.Symmetric.HSalsa20.fst \
		-drop 'Hacl.Spec.\*' -drop 'Hacl.Spe.\*' -drop 'Hacl.Cast' -drop 'Hacl.UInt.\*' \
		-drop Prims -drop FStar \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -skip-compilation  -ccopt -std=gnu99

XSalsa20.c: Hacl.Symmetric.XSalsa20.fst Hacl.Test.XSalsa20.fst
	mkdir -p salsa-c
	$(KREMLIN_HOME)/krml -tmpdir salsa-c -verbose \
		-I ../bignum -I ../lib/kremlin \
		Hacl.Symmetric.XSalsa20.fst Hacl.Test.XSalsa20.fst -o xsalsa20.exe -no-prefix Hacl.Test.XSalsa20 \
		-drop 'Hacl.Spec.\*' -drop 'Hacl.Spe.\*' -drop 'Hacl.Cast' -drop 'Hacl.UInt.\*' \
		-drop Prims -drop FStar \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -ldopt -flto -ccopt -march=native  -ccopt -std=gnu99 
	./xsalsa20.exe

extract-c: Chacha20.c Salsa20.c HSalsa20.c XSalsa20.c


clean:
	rm -rf *.exe *.exe.* *.out *~ salsa-c
