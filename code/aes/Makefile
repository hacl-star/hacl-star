include ../../Makefile.include

AES_FILES= $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/fst/Lib.RawIntTypes.fst \
	Hacl.Impl.Aes.BitSlice.fst \
	Hacl.Test.AesCBC.fst \
	Hacl.AesCBC.fst

AESNI_FILES= $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/fst/Lib.RawIntTypes.fst \
	Hacl.Impl.Aes.NI.fst \
	Hacl.Test.AesNI.fst \
	Hacl.AesCTR.fst 

# Files that are too slow and for which verification speed must improve
SLOW=

# Files that still have errors
TODO=

FSTAR_INCLUDES+=--include $(HACL_HOME)/code/bignum --include $(HACL_HOME)/code/curve25519 --include $(HACL_HOME)/code/hash

# Parameter for interactive mode
%.fst-in:
	@echo $(OPTIONS) --hint_info \
	$(FSTAR_INCLUDES)

ct: $(addsuffix -lax, $(AES_FILES))
	$(FSTAR) --lax --verify_all Hacl.Impl.Aes.fst
all-ct: ct

bignum-ver: $(addsuffix -reloc-verify, )
specific-ver: $(addsuffix -verify, $(filter-out $(SLOW) $(TODO), $(AES_FILES)))
verify: bignum-ver specific-ver
hints: bignum-hints specific-hints
all-ver: verify

# Hints regeneration
bignum-hints: $(addsuffix .reloc.hints, )
specific-hints: $(addsuffix .hints, $(AES_FILES))
hints: bignum-hints specific-hints
all-hints: hints

# For CI, all modules restricted from incomplete or slow ones
bignum-ci: $(addsuffix -reloc-verify, $(filter-out $(SLOW) $(TODO), ))
specific-ci: $(addsuffix -verify, $(filter-out $(SLOW) $(TODO), $(AES_FILES)))
ci: bignum-ci specific-ci
all-ci: ci

KREMLIN_ARGS=-warn-error +9 -I $(HACL_HOME)/lib/ -I $(HACL_HOME)/lib/fst -I $(KREMLIN_HOME)/kremlib -I $(HACL_HOME)/specs -I . -ccopt '-march=native'

aes-c/out.krml: $(AES_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir aes-c $(AES_FILES) -skip-translation

aes-c/Hacl_AesCBC.c: aes-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir aes-c $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -bundle 'Hacl.AesCBC=*'

extract-c: aes-c/Hacl_AesCBC.c

aes-bitslice.exe: aes-c/Hacl_AesCBC.c aes-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir aes-c  \
	  -no-prefix 'Hacl.Test.AesCBC' -minimal -add-include '"kremlib.h"' \
	  -bundle 'Hacl.Test.AesCBC=*' -library Hacl.AesCBC \
	  $^ -o $@


test: aes-bitslice.exe
	./$^


aesni-c/out.krml: $(AESNI_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir aesni-c $(AESNI_FILES) -skip-translation

aesni-c/Hacl_AesCTR.c: aesni-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir aesni-c  $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -add-include '"vec128.h"' -bundle 'Hacl.AesCTR=*'
aesni.exe: aesni-c/Hacl_AesCTR.c aesni-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir aesni-c \
	  -no-prefix 'Hacl.Test.AesNI' -minimal -add-include '"kremlib.h"' -add-include '"vec128.h"'\
	  -bundle 'Hacl.Test.AesNI=*' -library Hacl.AesCTR -library Lib.Vec128 \
	  $^ -o $@


GF128NI_FILES= $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/fst/Lib.RawIntTypes.fst \
	Hacl.Impl.Gf128.NI.fst \
	Hacl.Gf128.fst \
	Hacl.Test.Gf128NI.fst 

gf128ni-c/out.krml: $(GF128NI_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir gf128ni-c $(GF128NI_FILES) -skip-translation

gf128ni-c/Hacl_Gf128.c: gf128ni-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir gf128ni-c  $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -add-include '"vec128.h"' -bundle 'Hacl.Gf128=*'
gf128ni.exe: gf128ni-c/Hacl_Gf128.c gf128ni-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir gf128ni-c \
	  -no-prefix 'Hacl.Test.Gf128NI' -minimal -add-include '"kremlib.h"' -add-include '"vec128.h"'\
	  -bundle 'Hacl.Test.Gf128NI=*' -library Hacl.Gf128 -library Lib.Vec128 \
	  $^ -o $@




count-line:
	cloc --force-lang=ocaml $(AES_FILES)

clean:
	rm -rf *.exe *.exe.* *.out *~ aescbc-c aesni-c gf128ni-c *.graph
