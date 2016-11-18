FSTAR_HOME?=../../../FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
ARTIFACT_HOME=..
include $(ARTIFACT_HOME)/Makefile.include

INCLUDES=$(addprefix --include , ../lib)

# All the directory modules
MODULES= \
  Buffer.Utils \
  Crypto.Symmetric.Chacha20 \
  Crypto.Symmetric.Poly1305.Lemmas \
  Crypto.Symmetric.Poly1305.Spec \
  Crypto.Symmetric.Poly1305 \
  Crypto.Symmetric.Bytes \
  Crypto.Symmetric.GF128 \
  Crypto.Symmetric.GF128.Spec \
  Crypto.Symmetric.GCM \
  Crypto.Symmetric.MAC \
  Crypto.Symmetric.UF1CMA \
  Crypto.Symmetric.AES \
  Crypto.Symmetric.AES128 \
  Crypto.Symmetric.Cipher \
  Crypto.Symmetric.PRF \
  Crypto.Indexing \
  Crypto.Plain \
  Crypto.AEAD.BufferUtils \
  Crypto.AEAD.Encoding \
  Crypto.AEAD.Invariant \
  Crypto.AEAD.Lemmas \
  Crypto.AEAD.Lemmas.Part2 \
  Crypto.AEAD.Lemmas.Part3 \
  Crypto.AEAD.AES256GCM \
  Crypto.AEAD.Wrappers \
  Crypto.AEAD
#  Crypto.KrmlTest

OPTIONS=$(FSTAR_OPTIONS_VER)

%.fst-ver:
	$(FSTAR) $(OPTIONS) \
	$(FSTAR_INCLUDE_PATHS) \
	--__temp_no_proj Crypto.Symmetric.MAC \
	--include ../functional_correctness --include $(LIB_KRML) \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst

%.fst-in: 
	@echo $(OPTIONS) \
	$(FSTAR_INCLUDE_PATHS) \
	--__temp_no_proj Crypto.Symmetric.MAC \
	--include ../functional_correctness --include $(LIB_KRML) \
	--verify_module $(basename $(notdir $@))

ver: $(addsuffix .fst-ver, $(MODULES))

test: real/Flag.fst real/test_hacks.c Crypto.KrmlTest.fst
	$(KREMLIN) $(KREMLIN_ARGS) -I ../functional_correctness -no-prefix Crypto.KrmlTest \
		-add-include '"testlib.h"' \
		$(KREMTEST)/testlib.c -I $(LIB_KRML) -I $(KREMLIB) -I $(KREMTEST) \
		-tmpdir tmp -o test_aead.exe $^
	./test_aead.exe

clean:
	rm -f *~ *.exe
