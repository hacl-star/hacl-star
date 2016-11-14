FSTAR_HOME?=../../FStar
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
  Crypto.AEAD.AES256GCM \
  Crypto.Symmetric.PRF \
  Crypto.AEAD.Encoding \
  Crypto.AEAD.Invariant \
  Crypto.AEAD.Lemmas \
  Crypto.Plain \
  Crypto.AEAD

OPTIONS=--fstar_home $(FSTAR_HOME) --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3timeout 20

%.fst-verify:
	$(FSTAR) $(OPTIONS) \
	$(FSTAR_INCLUDE_PATHS) \
	--__temp_no_proj Crypto.Symmetric.MAC \
	--verify_module $(basename $(notdir $@)) \
	--include ../functional_correctness --include $(LIB_KRML) \
	$(basename $@).fst

ver: $(addsuffix .fst-verify, $(MODULES))

test: real/Flag.fst real/test_hacks.c Crypto.KrmlTest.fst
	$(KREMLIN) $(KREMLIN_ARGS) -I ../functional_correctness -no-prefix Crypto.KrmlTest \
		-add-include '"testlib.h"' \
		$(KREMTEST)/testlib.c -I $(LIB_KRML) -I $(KREMLIB) -I $(KREMTEST) \
		-tmpdir tmp -o test_aead.exe $^
	./test_aead.exe

clean:
	rm -f *~ *.exe
