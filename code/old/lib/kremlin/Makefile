include ../../Makefile.include

ALL= \
	FStar.Old.Endianness.fst \
	Hacl.Cast.fst \
	Hacl.Endianness.fst \
	Hacl.Policies.fst \
	Hacl.Spec.Endianness.fst \
	Hacl.Types.fst \
	Hacl.UInt128.fst \
	Hacl.UInt16.fst \
	Hacl.UInt32.fst \
	Hacl.UInt64.fst \
	Hacl.UInt8.fst

SLOW=
BROKEN=

ci: $(addsuffix -verify, $(filter-out $(SLOW) $(BROKEN), $(ALL)))
verify: $(addsuffix -verify, $(filter-out $(SLOW) $(BROKEN), $(ALL)))
hints: $(addsuffix .hints, $(ALL))
all-ver: verify
all-ct:
all-ci: ci
all-hints: hints

all: $(addsuffix -verify, $(ALL))

KREMLIN_ARGS+=-drop Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.Types

lib-c/Hacl_Policies.c: Hacl.Policies.fst
	$(KREMLIN) $(KREMLIN_ARGS) -skip-compilation $^ -tmpdir lib-c \
		-drop Hacl.UInt128,FStar

ccomp-c/FStar.h ccomp-c/FStar.c: $(FSTAR_HOME)/ulib/FStar.UInt128.fst \
	$(FSTAR_HOME)/ulib/FStar.Int.Cast.Full.fst \
	Hacl.UInt128.fst Hacl.Cast.fst
	$(KREMLIN) $(KREMLIN_ARGS) -skip-compilation $^  -fnostruct-passing -fnoanonymous-unions -tmpdir ccomp-c

# # JK: FIXME
# lib-c/FStar.h: $(FSTAR_HOME)/ulib/FStar.UInt128.fst $(FSTAR_HOME)/ulib/FStar.Int.Cast.Full.fst Hacl.UInt128.fst Hacl.Cast.fst
# 	$(KREMLIN) $(KREMLIN_ARGS) -skip-compilation $^ -fnouint128 -fnostruct-passing -fnoanonymous-unions -tmpdir lib-c
# 	@cat lib-c/FStar.c >> lib-c/FStar.h
# 	@sed -i 's/#include "kremlib.h"//g' lib-c/FStar.h
# 	@sed -i 's/#endif//g' lib-c/FStar.h
# 	@sed -i 's/#include "FStar.h"//g' lib-c/FStar.h
# 	@echo "#endif" >> lib-c/FStar.h
# 	@rm lib-c/Hacl_UInt128.*

# lib-c/Hacl_UInt128.h lib-c/Hacl_UInt128.c: Hacl.UInt128.fst Hacl.Cast.fst
# 	$(KREMLIN) $(KREMLIN_ARGS) -drop Prims,FStar -skip-compilation $^ -fnouint128 -fnoanonymous-unions -tmpdir lib-c -bundle "Hacl.UInt128=Hacl.UInt128,FStar.UInt128,Hacl.Cast,FStar.Int.Cast.Full" # -fnostruct-passing

lib-c/FStar.h lib-c/FStar.c: $(FSTAR_HOME)/ulib/FStar.UInt128.fst Hacl.UInt128.fst Hacl.Cast.fst
	$(KREMLIN) $(KREMLIN_ARGS) -drop Prims,FStar.Pervasives,FStar.PropositionalExtensionality,FStar.Set,FStar.Int,FStar.Int.Cast.Full,FStar.HyperStack,FStar.HyperStack.All -skip-compilation $^ -fparentheses -fnouint128 -fnoanonymous-unions -tmpdir lib-c # -fnostruct-passing

# lib-c/FStar_UInt128.h lib-c/FStar_UInt128.c: $(FSTAR_HOME)/ulib/FStar.UInt128.fst
# 	$(KREMLIN) $(KREMLIN_ARGS) -bundle "FStar.UInt128=FStar.UInt128" -drop Prims,FStar.Pervasives,FStar.PropositionalExtensionality,FStar.Set,FStar.Int,FStar.UInt,FStar.Int.Cast,FStar.HyperStack,FStar.HyperStack.All -skip-compilation $^ -fparentheses -fnouint128 -fnoanonymous-unions -tmpdir lib-c # -fnostruct-passing

extract-c: ccomp-c/FStar.h lib-c/Hacl_Policies.c

# JK: implement these for the library files
test: extract-c

clean:
	rm -rf *~ *.exe lib-c ccomp-c
