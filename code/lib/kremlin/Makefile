include ../../../Makefile.include

ALL=Hacl.UInt8.fst Hacl.UInt16.fst Hacl.UInt32.fst Hacl.UInt64.fst Hacl.UInt128.fst Hacl.Cast.fst

all: $(addsuffix -ver, $(ALL))

KREMLIN_ARGS=-drop Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.Types

lib-c/Hacl_Policies.c: Hacl.Policies.fst
	$(KREMLIN) $(KREMLIN_ARGS) -skip-compilation $^ -tmpdir lib-c \
		-drop Hacl.UInt128,FStar

# JK: FIXME
lib-c/FStar.h: $(FSTAR_HOME)/ulib/FStar.UInt128.fst $(FSTAR_HOME)/ulib/FStar.Int.Cast.Full.fst Hacl.UInt128.fst Hacl.Cast.fst
	$(KREMLIN) $(KREMLIN_ARGS) -skip-compilation $^ -fnouint128 -fnostruct-passing -fnoanonymous-unions -tmpdir lib-c
	@cat lib-c/FStar.c >> lib-c/FStar.h
	@sed -i 's/#include "kremlib.h"//g' lib-c/FStar.h
	@sed -i 's/#endif//g' lib-c/FStar.h
	@sed -i 's/#include "FStar.h"//g' lib-c/FStar.h
	@echo "#endif" >> lib-c/FStar.h
	@rm lib-c/Hacl_UInt128.*

# JK: FIXME
nss-c/FStar.h: $(FSTAR_HOME)/ulib/FStar.UInt128.fst $(FSTAR_HOME)/ulib/FStar.Int.Cast.Full.fst Hacl.UInt128.fst Hacl.Cast.fst
	$(KREMLIN) $(KREMLIN_ARGS) -skip-compilation $^ -fnouint128 -fnoanonymous-unions -tmpdir nss-c -fparentheses
	@cat nss-c/FStar.c >> nss-c/FStar.h
	@sed -i 's/#include "kremlib.h"//g' nss-c/FStar.h
	@sed -i 's/#endif//g' nss-c/FStar.h
	@sed -i 's/#include "FStar.h"//g' nss-c/FStar.h
	@echo "#endif" >> nss-c/FStar.h
	@rm nss-c/Hacl_UInt128.*

extract-c: lib-c/FStar.h lib-c/Hacl_Policies.c

%-ver: %
	$(FSTAR) $^

clean:
	rm -rf *~ *.exe lib-c nss-c
