FSTAR_HOME?=../../../../FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
ARTIFACT_HOME=..
include $(ARTIFACT_HOME)/Makefile.include

INCLUDES=$(addprefix --include , ../lib)

# All the directory modules (for efficient verification)
MODULES= \
  Buffer.Utils \
  Crypto.Symmetric.Chacha20 \
  Crypto.Symmetric.Poly1305.Lemmas \
  Crypto.Symmetric.Poly1305.Spec \
  Crypto.Symmetric.Poly1305 \
  Crypto.Symmetric.Bytes \
  Crypto.Symmetric.GF128 \
  Crypto.Symmetric.GCM \
  Crypto.Symmetric.AES \
  Crypto.Symmetric.AES128 \
  Crypto.Symmetric.Cipher \
  Crypto.Symmetric.PRF \
  Crypto.AEAD.Encoding \
  Crypto.AEAD.Invariant \
  Crypto.AEAD.Lemmas \
  Crypto.AEAD.AES256GCM \
  Crypto.Plain \
  Crypto.AEAD

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
