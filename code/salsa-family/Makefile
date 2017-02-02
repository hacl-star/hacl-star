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

%.fst-c: %.fst
	mkdir -p salsa-c
	$(KREMLIN_HOME)/krml -tmpdir salsa-c -verbose \
		-I ../bignum -I ../lib/kremlin \
		$^ -o $(basename $^).exe -no-prefix $(basename $^) \
		-drop 'Hacl.Spec.\*' -drop 'Hacl.Spe.\*' -drop 'Hacl.Cast' -drop 'Hacl.UInt.\*' \
		-drop Prims -drop FStar \
		$(KREMLIN_HOME)/kremlib/testlib.c -add-include '"testlib.h"' \
                -no-prefix Hacl.Test.Poly1305_64 -ldopt -flto -ccopt -march=native -o poly1305.exe
	./$(basename $^).exe

extract-c: $(addsuffix -c, $(SALSA_FILES))


clean:
	rm -rf *.exe *.exe.* *.out *~ salsa-c
