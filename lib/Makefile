include ../Makefile.include

CACHE_DIR     = .cache
OUTPUT_DIR    = .output
HINT_DIR      = .hints

all: verify

FSTAR_INCLUDE_DIRS = \
  $(KREMLIN_HOME)/kremlib \
  $(HACL_HOME)/lib \
  $(HACL_HOME)/lib/fst

FSTAR_INCLUDES = $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(OTHERFLAGS) \
  --cache_checked_modules --cache_dir $(CACHE_DIR) \
  --odir $(OUTPUT_DIR) $(FSTAR_INCLUDES)

FILES = $(addprefix fst/, \
	Lib.IntTypes.fst \
	Lib.Sequence.fst \
	Lib.Buffer.fst)

FIXME = $(addprefix fst/, \
	Lib.RawIntTypes.fst \
	Lib.IntVector.fst \
	Lib.ByteSequence.fst \
	Lib.Endianness.fst \
	Lib.LoopCombinators.fst)

%.fst-verify:
	$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_INCLUDES) $^ --use_hints

%.fsti-verify:
	$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_INCLUDES) $^ --use_hints

%.fst-hints:
	$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_INCLUDES) $^ --record_hints

%.fsti-hints:
	$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_INCLUDES) $^ --record_hints


verify: $(addsuffix -verify, $(FILES))
hints: $(addsuffix -hints, $(FILES))
