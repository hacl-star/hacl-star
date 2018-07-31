include ../../Makefile.include

AES_FILES=  Hacl.Impl.Aes128.fst \
	Hacl.Test.Aes128.fst \
	Hacl.Aes128.fst

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

KREMLIN_ARGS+=-tmpdir aes128-c \
		-I ../bignum -I ../curve25519 -I ../hash \

aes128-c/out.krml: $(AES_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) $(AES_FILES) -skip-translation

aes128-c/Hacl_Aes128.c: aes128-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -bundle 'Hacl.Aes128=*'

extract-c: aes128-c/Hacl_Aes128.c

aes128.exe: aes128-c/Hacl_Aes128.c aes128-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) \
	  -no-prefix 'Hacl.Test.Aes128' -minimal -add-include '"kremlib.h"' \
	  -bundle 'Hacl.Test.Aes128=*' -library Hacl.Aes128 \
	  $^ -o $@


test: aes128.exe
	./$^

count-line:
	cloc --force-lang=ocaml $(AES128_FILES)

clean:
	rm -rf *.exe *.exe.* *.out *~ aes128-c *.graph
