include ../../Makefile.include

AES_FILES= $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/fst/Lib.RawIntTypes.fst \
	Hacl.Impl.Aes.fst \
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

KREMLIN_ARGS=-warn-error +9 -I $(HACL_HOME)/lib/ -I $(HACL_HOME)/lib/fst -I $(KREMLIN_HOME)/kremlib -I $(HACL_HOME)/specs -I . -tmpdir aescbc-c \
		-I ../bignum -I ../curve25519 -I ../hash \

aescbc-c/out.krml: $(AES_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) $(AES_FILES) -skip-translation

aescbc-c/Hacl_AesCBC.c: aescbc-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -bundle 'Hacl.AesCBC=*'

extract-c: aescbc-c/Hacl_AesCBC.c

aescbc.exe: aescbc-c/Hacl_AesCBC.c aescbc-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) \
	  -no-prefix 'Hacl.Test.AesCBC' -minimal -add-include '"kremlib.h"' \
	  -bundle 'Hacl.Test.AesCBC=*' -library Hacl.AesCBC \
	  $^ -o $@


test: aescbc.exe
	./$^


KREMLIN_ARGS=-warn-error +9 -I $(HACL_HOME)/lib/ -I $(HACL_HOME)/lib/fst -I $(KREMLIN_HOME)/kremlib -I $(HACL_HOME)/specs -I . -tmpdir aesni-c -ccopt '-march=native' 


aesni-c/out.krml: $(AESNI_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) $(AESNI_FILES) -skip-translation

aesni-c/Hacl_AesCTR.c: aesni-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -add-include '"vec128.h"' -bundle 'Hacl.AesCTR=*'
aesni.exe: aesni-c/Hacl_AesCTR.c aesni-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) \
	  -no-prefix 'Hacl.Test.AesNI' -minimal -add-include '"kremlib.h"' -add-include '"vec128.h"'\
	  -bundle 'Hacl.Test.AesNI=*' -library Hacl.AesCTR -library Lib.Vec128 \
	  $^ -o $@


count-line:
	cloc --force-lang=ocaml $(AES_FILES)

clean:
	rm -rf *.exe *.exe.* *.out *~ aescbc-c *.graph
