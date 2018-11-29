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
	Lib.RawIntTypes.fst \
	Lib.Sequence.fst \
	Lib.ByteSequence.fst \
	Lib.Buffer.fst \
	Lib.ByteBuffer.fst \
	Lib.LoopCombinators.fst )

FIXME = $(addprefix fst/, \
	Lib.IntVector.fst )

%.fst-v: %.fst
	$(FSTAR) $(FSTAR_INCLUDES) --use_hints $<

%.fsti-v: %.fsti
	$(FSTAR) $(FSTAR_INCLUDES) --use_hints $<

%.fst-h: %.fst
	$(FSTAR) $(FSTAR_INCLUDES) --record_hints $<

%.fsti-h: %.fsti
	$(FSTAR) $(FSTAR_INCLUDES) --record_hints $<


verify: $(addsuffix -v, $(FILES))
hints: $(addsuffix -h, $(FILES))
