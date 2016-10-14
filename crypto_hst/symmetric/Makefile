FSTAR_HOME?=../../../FStar
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe

LIB_DIR=../../lib/hst

OPTIONS_VER=--include $(LIB_DIR) --use_hints

LIB_FILES=Hacl.Cast.fst Hacl.SBuffer.fst Hacl.UInt128.fst Hacl.UInt64.fst Hacl.UInt32.fst Hacl.UInt8.fst

all: chacha poly aead-aes256-gcm

import-lib:
	@cp $(addprefix ../../lib/hst/, $(LIB_FILES)) .

import-kremlin:
	@cp $(addprefix ../../lib/hst/kremlin/, $(LIB_FILES)) .

chacha: Hacl.Symmetric.Chacha20.fst-ver

aes: Hacl.Symmetric.AES.fst-ver

poly: $(addsuffix -ver, \
		Utils.fst \
		Hacl.Symmetric.Poly1305.Bigint.fst \
		Hacl.Symmetric.Poly1305.Bignum.fst \
		Hacl.Symmetric.Poly1305.fst)

gcm: Hacl.Symmetric.GCM.fst-ver

aead-aes256-gcm: aes gcm Hacl.AEAD.AES256GCM.fst-ver

%-ver: %
	$(FSTAR) $(OPTIONS_VER) $^


clean:
	rm -f *~ $(addprefix ml/, *.cmo *.cmi *.o *~ *.cmx) $(LIB_FILES)
