# FStar variables
FSTAR_HOME?=../../../FStar
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_DEFAULT_ARGS) # from the included Makefile

OPTIONS_VER=

LIB_DIR=../../lib/st
LIB_FILES=$(addprefix $(LIB_DIR)/, axioms.fst intlib.fst IntLibLemmas.fst sint.fst sbuffer.fst SInt.UInt8.fst SInt.UInt32.fst SInt.UInt63.fst SInt.UInt64.fst SInt.Cast.fst SBytes.fst)

.PHONY: lib-ver

all: lib-ver curve-lax

# Verification target for the low-level libraries of F* in universes
lib-ver:
	$(FSTAR) $(OPTIONS_VER) $(LIB_FILES)

# Curve25519 lax typechecking
curve-lax:
	$(FSTAR) $(OPTIONS_VER) $(LIB_FILES) Curve.Ladder.fst --lax

# Cleaning
clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	@rm -f *~

