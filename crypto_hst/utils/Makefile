# FStar variables
FSTAR_HOME?=../../../FStar
FSTAR=$(FSTAR_HOME)/bin/fstar.exe

# Libraries
LIB_DIR_HST=../../lib/hst
LIB_FILES_HST= Math.Axioms.fst Math.Lib.fst Math.Lemmas.fst Hacl.UInt8.fst Hacl.UInt32.fst Hacl.UInt64.fst Hacl.UInt128.fst Hacl.SBuffer.fst Hacl.Cast.fst

# Modules
FILES= Hacl.Operations.fst Hacl.Conversions.fst


.PHONY: prepare lax ver clean

all: lax

prepare:
	cp $(LIB_DIR_HST)/*.fst .

lax: prepare
	$(FSTAR) --lax $(FILES)

ver:
	$(FSTAR) $(FILES)

clean:
	rm -f *~ $(LIB_FILES_HST)
