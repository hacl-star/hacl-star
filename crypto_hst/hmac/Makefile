# FStar variables
FSTAR_HOME?=../../../FStar
FSTAR=$(FSTAR_HOME)/bin/fstar.exe

# Libraries
LIB_DIR_HST=../../lib/hst
LIB_FILES_HST= Math.Axioms.fst Math.Lib.fst Math.Lemmas.fst Hacl.UInt8.fst Hacl.UInt32.fst Hacl.UInt64.fst Hacl.UInt128.fst Hacl.SBuffer.fst Hacl.Cast.fst

# Utils 
UTILS_DIR_HST=../utils
UTILS_FILES_HST= Hacl.Operations.fst Hacl.Operations.Pure.fst Hacl.Conversions.fst


# Dependencies
SHA256_DIR=../sha
SHA256_HST=Hash.Sha256.fst


.PHONY: prepare lax ver clean

all: lax

prepare:
	cp $(LIB_DIR_HST)/*.fst .
	cp $(UTILS_DIR_HST)/*.fst .
	cp $(SHA256_DIR)/$(SHA256_HST) .

lax: prepare
	$(FSTAR) --lax HMAC.fst
	$(FSTAR) --lax HMAC.B.fst
	#$(FSTAR) --lax HMAC.Pure.fst
	#$(FSTAR) --lax HMAC.Pure.2.fst

ver:
	#$(FSTAR) HMAC.fst
	$(FSTAR) HMAC.B.fst
	#$(FSTAR) HMAC.Pure.fst
	#$(FSTAR) HMAC.Pure.2.fst

clean:
	rm -f *~ $(LIB_FILES_HST) $(UTILS_FILES_HST) $(SHA256_HST)

