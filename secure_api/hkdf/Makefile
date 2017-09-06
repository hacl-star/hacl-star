HACL_HOME?=../..
FSTAR_HOME?=../../../FStar
KREMLIN_HOME?=../../../kremlin
include ../Makefile

KRML_ARGS=$(FPIC) -ccopt -maes -fnouint128 \
  $(KREMLIN_HOME)/test/../kremlib/testlib.c \
  -drop Hacl.Spe.*,Spec,Hacl.Spec,Spec.*,Hacl.Spec.* \
  -add-include '"testlib.h"' -bundle Hacl.* $(KOPTS)

tmp/out.krml: Crypto.Test.HMAC.fst
	$(KRML) ../test/test_hacl/Crypto.Indexing.fst Crypto.Test.HMAC.fst \
	  -tmpdir tmp -skip-translation

test-hmac.exe: tmp/out.krml
	$(KRML) $< -tmpdir tmp -o $@ -no-prefix Crypto.Test.HMAC
	./$@	
