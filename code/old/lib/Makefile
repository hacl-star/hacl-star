include ../Makefile.include

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

extract-c:

test:

clean:
