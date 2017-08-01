# FSTAR_HOME?=../../../dependencies/FStar
# FSTAR?=$(FSTAR_HOME)/bin/fstar.exe
# FSTAR_ARGS=
include ../../Makefile.include

ALL=Hacl.UInt8.fst Hacl.UInt16.fst Hacl.UInt32.fst Hacl.UInt64.fst Hacl.UInt128.fst Hacl.Cast.fst

all: $(addsuffix -ver, $(ALL))

KREMLIN_ARGS=-tmpdir lib-c -drop Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.Types

lib-c/Hacl_Policies.c: Hacl.Policies.fst
	$(KREMLIN) $(KREMLIN_ARGS) -skip-compilation $^ \
		-drop Hacl.UInt128,FStar

lib-c/FStar.h: $(FSTAR_HOME)/ulib/FStar.UInt128.fst $(FSTAR_HOME)/ulib/FStar.Int.Cast.Full.fst Hacl.UInt128.fst Hacl.Cast.fst
	$(KREMLIN) $(KREMLIN_ARGS) -skip-compilation $^ -fnouint128 -fnostruct-passing -fnoanonymous-unions
	@cat lib-c/FStar.c >> lib-c/FStar.h
	@sed -i 's/#include "kremlib.h"//g' lib-c/FStar.h
	@sed -i 's/#endif//g' lib-c/FStar.h
	@sed -i 's/#include "FStar.h"//g' lib-c/FStar.h
	@echo "#endif" >> lib-c/FStar.h
	@rm lib-c/Hacl_UInt128.*

script.exe: script.ml
	ocamlopt str.cmxa $^ -o script.exe

test: script.exe
	./$^

extract-c: lib-c/FStar.h lib-c/Hacl_Policies.c

%-ver: %
	$(FSTAR) $^

clean:
	rm -rf *~ *.exe lib-c
