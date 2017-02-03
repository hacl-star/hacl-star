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


%.fst-verify: %.fst
	$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib $^ --use_hints

verify: $(addsuffix -verify, $(SALSA_FAMILY_FILES))


%.fst-hints: %.fst
	$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib $^ --record_hints

hints: $(addsuffix -hints, $(SALSA_FAMILY_FILES))

Chacha20.c: Hacl.Symmetric.Chacha20.fst Hacl.Test.Chacha20.fst Chacha20.fst
	mkdir -p salsa-c
	$(KREMLIN_HOME)/krml -tmpdir salsa-c -verbose \
		-I ../bignum -I ../lib/kremlin \
		Hacl.Symmetric.Chacha20.fst Hacl.Test.Chacha20.fst -o chacha20.exe -no-prefix Hacl.Test.Chacha20 \
		-drop 'Hacl.Spec.\*' -drop 'Hacl.Spe.\*' -drop 'Hacl.Cast' -drop 'Hacl.UInt.\*' \
		-drop Prims -drop FStar \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -ldopt -flto -ccopt -march=native 
	$(KREMLIN_HOME)/krml -tmpdir salsa-c -verbose \
		-I ../bignum -I ../lib/kremlin \
		Hacl.Symmetric.Chacha20.fst Chacha20.fst -o chacha20.exe \
		-drop 'Hacl.Spec.\*' -drop 'Hacl.Spe.\*' -drop 'Hacl.Cast' -drop 'Hacl.UInt.\*' \
		-drop Prims -drop FStar \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -skip-compilation
	./chacha20.exe

Salsa20.c: Hacl.Symmetric.Salsa20.fst Hacl.Test.Salsa20.fst
	mkdir -p salsa-c
	$(KREMLIN_HOME)/krml -tmpdir salsa-c -verbose \
		-I ../bignum -I ../lib/kremlin \
		Hacl.Symmetric.Salsa20.fst Hacl.Test.Salsa20.fst -o salsa20.exe -no-prefix Hacl.Test.Salsa20 \
		-drop 'Hacl.Spec.\*' -drop 'Hacl.Spe.\*' -drop 'Hacl.Cast' -drop 'Hacl.UInt.\*' \
		-drop Prims -drop FStar \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -ldopt -flto -ccopt -march=native 
	./salsa20.exe

HSalsa20.c: Hacl.Symmetric.HSalsa20.fst 
	mkdir -p salsa-c
	$(KREMLIN_HOME)/krml -tmpdir salsa-c -verbose \
		-I ../bignum -I ../lib/kremlin \
		Hacl.Symmetric.HSalsa20.fst \
		-drop 'Hacl.Spec.\*' -drop 'Hacl.Spe.\*' -drop 'Hacl.Cast' -drop 'Hacl.UInt.\*' \
		-drop Prims -drop FStar \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -skip-compilation

XSalsa20.c: Hacl.Symmetric.XSalsa20.fst Hacl.Test.XSalsa20.fst
	mkdir -p salsa-c
	$(KREMLIN_HOME)/krml -tmpdir salsa-c -verbose \
		-I ../bignum -I ../lib/kremlin \
		Hacl.Symmetric.XSalsa20.fst Hacl.Test.XSalsa20.fst -o xsalsa20.exe -no-prefix Hacl.Test.XSalsa20 \
		-drop 'Hacl.Spec.\*' -drop 'Hacl.Spe.\*' -drop 'Hacl.Cast' -drop 'Hacl.UInt.\*' \
		-drop Prims -drop FStar \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' -ldopt -flto -ccopt -march=native 
	./xsalsa20.exe

extract-c: Chacha20.c Salsa20.c HSalsa20.c XSalsa20.c


clean:
	rm -rf *.exe *.exe.* *.out *~ salsa-c
