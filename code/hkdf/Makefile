# FStar variables
FSTAR_HOME?=../../../FStar
FSTAR=$(FSTAR_HOME)/bin/fstar.exe

# Libraries
LIB_DIR_HST=../../lib/hst
LIB_FILES_HST= Math.Axioms.fst Math.Lib.fst Math.Lemmas.fst Hacl.UInt8.fst Hacl.UInt32.fst Hacl.UInt64.fst Hacl.UInt128.fst Hacl.SBuffer.fst Hacl.Cast.fst


# Dependencies
SHA256_DIR=../sha
SHA256_HST=Hash.Sha256.fst
HMAC_SHA256_DIR=../hmac
HMAC_SHA256_HST=HMAC.SHA2.fst


.PHONY: prepare lax ver clean

all: lax

prepare:
	cp $(LIB_DIR_HST)/*.fst .
	cp $(SHA256_DIR)/$(SHA256_HST) .
	cp $(HMAC_SHA256_DIR)/$(HMAC_SHA256_HST) .

lax: prepare
	$(FSTAR) --lax HKDF.Sha256.fst --include ../utils

ver:
	$(FSTAR) HKDF.Sha256.fst

clean:
	rm -f *~ $(LIB_FILES_HST) $(SHA256_HST) $(HMAC_SHA256_HST)
