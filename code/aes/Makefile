include ../../Makefile.include

AES_BS_FILES= $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/fst/Lib.RawIntTypes.fst \
	Hacl.Impl.Aes.BitSlice.fst \
	Hacl.Test.AesCTR.BitSlice.fst \
	Hacl.AesCTR.fst

AES_NI_FILES= $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/fst/Lib.RawIntTypes.fst \
	Hacl.Impl.Aes.NI.fst \
	Hacl.Test.AesCTR.NI.fst \
	Hacl.AesCTRNI.fst



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


aes-bitslice-c/out.krml: $(AES_BS_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir aes-bitslice-c $(AES_BS_FILES) -skip-translation

aes-bitslice-c/Hacl_AesCTR.c: aes-bitslice-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir aes-bitslice-c $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -bundle 'Hacl.AesCTR=*'

extract-c: aes-bitslice-c/Hacl_AesCTR.c

aes-bitslice.exe: aes-bitslice-c/Hacl_AesCTR.c aes-bitslice-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir aes-bitslice-c  \
	  -no-prefix 'Hacl.Test.AesCTR.BitSlice' -minimal -add-include '"kremlib.h"' \
	  -bundle 'Hacl.Test.AesCTR.BitSlice=*' -library Hacl.AesCTR \
	  $^ -o $@

aes-ni-c/out.krml: $(AES_NI_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir aes-ni-c $(AES_NI_FILES) -skip-translation

aes-ni-c/Hacl_AesCTRNI.c: aes-ni-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir aes-ni-c  $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -add-include '"vec128.h"' -bundle 'Hacl.AesCTRNI=*'
aes-ni.exe: aes-ni-c/Hacl_AesCTRNI.c aes-ni-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir aes-ni-c \
	  -no-prefix 'Hacl.Test.AesCTR.NI' -minimal -add-include '"kremlib.h"' -add-include '"vec128.h"'\
	  -bundle 'Hacl.Test.AesCTR.NI=*' -library Hacl.AesCTRNI -library Lib.Vec128 \
	  $^ -o $@

aes-test: aes-bitslice.exe aes-ni.exe
	./aes-bitslice.exe
	./aes-ni.exe

aes-perf: aes-bitslice.exe aes-ni.exe
	gcc-8 -march=native -mtune=native -Ofast -flto -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . aes-bitslice-c/Hacl_AesCTR.c aes-ni-c/Hacl_AesCTRNI.c $(KREMLIN_HOME)/kremlib/c/testlib.o aes_test.c -o aes-perf.exe
	./aes-perf.exe


GF128_NI_FILES= $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/fst/Lib.RawIntTypes.fst \
	Hacl.Impl.Gf128.NI.fst \
	Hacl.Gf128.fst \
	Hacl.Test.Gf128NI.fst 

gf128-ni-c/out.krml: $(GF128_NI_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir gf128-ni-c $(GF128_NI_FILES) -skip-translation

gf128-ni-c/Hacl_Gf128.c: gf128-ni-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir gf128-ni-c  $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -add-include '"vec128.h"' -bundle 'Hacl.Gf128=*'
gf128-ni.exe: gf128-ni-c/Hacl_Gf128.c gf128-ni-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir gf128-ni-c \
	  -no-prefix 'Hacl.Test.Gf128NI' -minimal -add-include '"kremlib.h"' -add-include '"vec128.h"'\
	  -bundle 'Hacl.Test.Gf128NI=*' -library Hacl.Gf128 -library Lib.Vec128 \
	  $^ -o $@


GF128_PRE_FILES= $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/fst/Lib.RawIntTypes.fst \
	Hacl.Impl.Gf128.PreComp.fst \
	Hacl.Gf128.PreComp.fst \
	Hacl.Test.Gf128PreComp.fst 

gf128-pre-c/out.krml: $(GF128_PRE_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir gf128-pre-c $(GF128_PRE_FILES) -skip-translation

gf128-pre-c/Hacl_Gf128_PreComp.c: gf128-pre-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir gf128-pre-c  $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -add-include '"vec128.h"' -bundle 'Hacl.Gf128.PreComp=*'
gf128-pre.exe: gf128-pre-c/Hacl_Gf128_PreComp.c gf128-pre-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir gf128-pre-c \
	  -no-prefix 'Hacl.Test.Gf128PreComp' -minimal -add-include '"kremlib.h"' -add-include '"vec128.h"'\
	  -bundle 'Hacl.Test.Gf128PreComp=*' -library Hacl.Gf128.PreComp -library Lib.Vec128 \
	  $^ -o $@

gf128-test: gf128-ni.exe gf128-pre.exe
	./gf128-ni.exe
	./gf128-pre.exe

gf128-perf: gf128-ni.exe gf128-pre.exe
	gcc-8 -march=native -mtune=native -Ofast -flto -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . gf128-ni-c/Hacl_Gf128.c  gf128-pre-c/Hacl_Gf128_PreComp.c $(KREMLIN_HOME)/kremlib/c/testlib.o gf128_test.c -o gf128-perf.exe
	./gf128-perf.exe


all: aes-bitslice.exe aes-ni.exe gf128ni.exe


count-line:
	cloc --force-lang=ocaml $(AES_FILES)

clean:
	rm -rf *.exe *.exe.* *.out *~ aescbc-c aesni-c gf128ni-c *.graph
