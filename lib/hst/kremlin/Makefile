FSTAR_HOME?=../../../../FStar
FSTAR?=$(FSTAR_HOME)/bin/fstar.exe
FSTAR_ARGS=

ALL=Hacl.UInt8.fst Hacl.UInt16.fst Hacl.UInt32.fst Hacl.UInt64.fst Hacl.UInt128.fst

all: $(addsuffix -ver, $(ALL))

%-ver: %
	$(FSTAR) $^
