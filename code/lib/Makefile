FSTAR_HOME?=../../../FStar
HYPERSTACK=$(FSTAR_HOME)/ulib/hyperstack
FSTAR=$(FSTAR_HOME)/bin/fstar.exe --include $(HYPERSTACK)

OPTIONS_VER=

ALL=Hacl.SBuffer.fst Hacl.UInt8.fst Hacl.UInt16.fst Hacl.UInt32.fst Hacl.UInt64.fst Hacl.UInt128.fst Hacl.Cast.fst

all: $(addsuffix -ver, $(ALL))

%-ver: %
	$(FSTAR) $^

clean:
	rm -f *~ $(addprefix ml/, *.cmo *.cmi *.o *~ *.cmx)
