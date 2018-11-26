include ../../../Makefile.include

AES_BS_FILES= $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/fst/Lib.RawIntTypes.fst \
	Hacl.Impl.Aes.CoreBitSlice.fst \
	Hacl.Impl.Aes.Core.fst \
	Hacl.Impl.Aes.Generic.fst \
	Hacl.Impl.Aes.BitSlice.fst \
	Hacl.Test.AesCTR.BitSlice.fst \
	Hacl.AesCTR.fst


AES_ONLY_FILES= $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/fst/Lib.RawIntTypes.fst \
	Hacl.Impl.Aes.CoreNI.fst \
	Hacl.Impl.Aes.Core.fst \
	Hacl.Impl.Aes.Generic.fst \
	Hacl.Impl.Aes.NI.fst \
	Hacl.AesNI.fst 


AES_NI_FILES= $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/fst/Lib.RawIntTypes.fst \
	Hacl.Impl.Aes.CoreNI.fst \
	Hacl.Impl.Aes.Core.fst \
	Hacl.Impl.Aes.Generic.fst \
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

KREMLIN_ARGS=-funroll-loops 8 -warn-error +9 -I $(HACL_HOME)/lib/ -I $(HACL_HOME)/lib/fst -I $(KREMLIN_HOME)/kremlib -I $(HACL_HOME)/specs -I . -ccopt '-march=native' 


aes-bitslice-c/out.krml: $(AES_BS_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir aes-bitslice-c $(AES_BS_FILES) -skip-translation

aes-bitslice-c/Hacl_AesCTR.c: aes-bitslice-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir aes-bitslice-c $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -bundle 'Hacl.AesCTR=*'


aes-only-c/out.krml: $(AES_ONLY_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir aes-only-c $(AES_ONLY_FILES) -skip-translation

aes-only-c/Hacl_AesNI.c: aes-only-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir aes-only-c $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -bundle 'Hacl.AesNI=*'


aes-bitslice-old-c/out.krml: $(AES_BS_OLD_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir aes-bitslice-old-c $(AES_BS_OLD_FILES) -skip-translation

aes-bitslice-old-c/Hacl_AesCTR_Old.c: aes-bitslice-old-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir aes-bitslice-old-c $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -bundle 'Hacl.AesCTR.Old=*'

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
	   -minimal -add-include '"kremlib.h"' -add-include '"vec128.h"' -drop Lib.Vec128 -bundle 'Hacl.AesCTRNI=*'

aes-ni.exe: aes-ni-c/Hacl_AesCTRNI.c aes-ni-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir aes-ni-c \
	  -no-prefix 'Hacl.Test.AesCTR.NI' -minimal -add-include '"kremlib.h"' -add-include '"vec128.h"'\
	  -bundle 'Hacl.Test.AesCTR.NI=*' -library Hacl.AesCTRNI -library Lib.Vec128 -drop Lib.Vec128 \
	  $^ -o $@

aes-test: aes-bitslice.exe aes-ni.exe
	./aes-bitslice.exe
	./aes-ni.exe

aes-perf: aes-bitslice.exe aes-ni.exe
	gcc-8 -march=native -mtune=native -Ofast -flto -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . aes-bitslice-c/Hacl_AesCTR.c aes-ni-c/Hacl_AesCTRNI.c $(KREMLIN_HOME)/kremlib/c/testlib.o aes_test.c -o aes-perf.exe
	./aes-perf.exe


GF128_OLD_NI_FILES= $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/fst/Lib.RawIntTypes.fst \
	Hacl.Impl.Gf128.NI.fst \
	Hacl.Gf128.fst \
	Hacl.Test.Gf128NI.fst 

GF128_NI_FILES= $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/fst/Lib.RawIntTypes.fst \
	Hacl.Impl.Gf128.FieldNI.fst \
	Hacl.Impl.Gf128.Generic.fst \
	Hacl.Gf128.NI.fst \
	Hacl.Test.Gf128.NI.fst 

gf128-ni-c/out.krml: $(GF128_NI_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir gf128-ni-c $(GF128_NI_FILES) -skip-translation

gf128-ni-c/Hacl_Gf128_NI.c: gf128-ni-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir gf128-ni-c  $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -add-include '"vec128.h"' -drop Lib.Vec128 -bundle 'Hacl.Gf128.NI=*'
gf128-ni.exe: gf128-ni-c/Hacl_Gf128_NI.c gf128-ni-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir gf128-ni-c \
	  -no-prefix 'Hacl.Test.Gf128.NI' -minimal -add-include '"kremlib.h"' -add-include '"vec128.h"'\
	  -bundle 'Hacl.Test.Gf128.NI=*' -library Hacl.Gf128 -library Lib.Vec128 -drop Lib.Vec128 \
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

gf128-perf: 
	gcc-8 -march=native -mtune=native -Ofast -flto -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . gf128-ni-c/Hacl_Gf128_NI.c  gf128-pre-c/Hacl_Gf128_PreComp.c $(KREMLIN_HOME)/kremlib/c/testlib.o gf128_test.c -o gf128-perf.exe
	./gf128-perf.exe


AESGCM_NI_FILES= $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/fst/Lib.RawIntTypes.fst \
	Hacl.Impl.Aes.CoreNI.fst \
	Hacl.Impl.Aes.Core.fst \
	Hacl.Impl.Aes.Generic.fst \
	Hacl.Impl.Aes.NI.fst \
	Hacl.Impl.Gf128.FieldNI.fst \
	Hacl.Impl.Gf128.Generic.fst \
	Hacl.Impl.Gf128.NI.fst \
	Hacl.Impl.AesGCM.fst \
	Hacl.Test.AesGCM.fst 

aesgcm-ni-c/out.krml: $(AESGCM_NI_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir aesgcm-ni-c $(AESGCM_NI_FILES) -skip-translation

aesgcm-ni-c/Hacl_Impl_AesGCM.c: aesgcm-ni-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir aesgcm-ni-c  $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -add-include '"vec128.h"' -bundle 'Hacl.Impl.AesGCM=*'
aesgcm-ni.exe: aesgcm-ni-c/Hacl_Impl_AesGCM.c aesgcm-ni-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir aesgcm-ni-c \
	  -no-prefix 'Hacl.Test.AesGCM' -minimal -add-include '"kremlib.h"' -add-include '"vec128.h"'\
	  -bundle 'Hacl.Test.AesGCM=*' -library Hacl.AesGCM -library Lib.Vec128 \
	  $^ -o $@
aesgcm-test: aesgcm-ni.exe
	./aesgcm-ni.exe

aesgcm-perf: 
	gcc-8 -march=native -mtune=native -Ofast -flto -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . aesgcm-ni-c/Hacl_Impl_AesGCM.c $(KREMLIN_HOME)/kremlib/c/testlib.o aesgcm_test.c -o aesgcm-perf.exe
	./aesgcm-perf.exe

aesgcm-test-only: 
	gcc-8 -march=native -mtune=native -Ofast -flto -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . aesgcm-ni-c/Hacl_Impl_AesGCM.c aesgcm-ni-c/Hacl_Test_AesGCM.c $(KREMLIN_HOME)/kremlib/c/testlib.o -o aesgcm-ni.exe
	./aesgcm-ni.exe

CURVE25519_FILES= $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/fst/Lib.RawIntTypes.fst \
	$(HACL_HOME)/lib/fst/Lib.Buffer.fst \
	$(HACL_HOME)/lib/fst/Lib.ByteBuffer.fst \
	$(HACL_HOME)/lib/c/Lib.Loops.fst \
	Hacl.Impl.Curve25519.Field64.fst \
	Hacl.Impl.Curve25519.Field51.fst \
	Hacl.Impl.Curve25519.Fields.fst \
	Hacl.Impl.Curve25519.Generic.fst 


KREMLIN_ARGS:=-funroll-loops 8 -warn-error +9 -I $(HACL_HOME)/lib/ -I $(HACL_HOME)/lib/fst -I $(KREMLIN_HOME)/kremlib -I $(HACL_HOME)/specs -I . -ccopt '-march=native' -fbuiltin-uint128 -drop FStar.UInt128 -fnocompound-literals -fc89-scope -fparentheses -fcurly-braces



curve64-perf:
	$(CC) -march=native -mtune=native -O3 -I rfc7748_precomputed/include/ rfc7748_precomputed/src/fp25519_x64.c -c -o fp25519.o 
	$(CC) -march=native -mtune=native -O3 -I rfc7748_precomputed/include/ rfc7748_precomputed/src/x25519_x64.c -c -o x25519.o 
	$(CC) -march=native -mtune=native -O3 vale/obj/curve25519-macos.S -c -o vale25519.o 
	$(CC) -march=native -mtune=native -O3 -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . curve64-c/Hacl_Curve25519_64.c $(KREMLIN_HOME)/kremlib/c/testlib.o curve64-test.c -o curve64-perf.exe rfc7748_precomputed/build/lib/librfc7748_precomputed.a vale25519.o fp25519.o x25519.o
	./curve64-perf.exe

curve-perf: 
	$(CC) -march=native -mtune=native -O3 -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . curve51-c/Hacl_Curve25519_51.c $(KREMLIN_HOME)/kremlib/c/testlib.o curvetest.c -o curve-perf.exe
	./curve-perf.exe

curve-snap: 
	$(CC) -O3 -march=native -mtune=native -I ../../snapshots/kremlib -I . curve25519-donna-c64.c Hacl_Curve25519.c curve51-c/Hacl_Curve25519_51.c curve64-c/Hacl_Curve25519_64.c $(KREMLIN_HOME)/kremlib/c/testlib.o curve-snap-test.c -o curve-snap.exe ~/Desktop/repositories/openssl/libcrypto.a rfc7748_precomputed/build/lib/librfc7748_precomputed.a vale/fp25519.o 
	./curve-snap.exe


POLY1305_64_FILES= $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/fst/Lib.RawIntTypes.fst \
	Lib.Utils.fst \
	Hacl.Impl.Poly1305.Field64.fst \
	Hacl.Impl.Poly1305.Fields.fst \
	Hacl.Impl.Poly1305.fst \
	Hacl.Poly1305_64.fst \
	Hacl.Test.Poly1305_64.fst 


KREMLIN_ARGS:=-funroll-loops 8 -warn-error +9 -I $(HACL_HOME)/lib/ -I $(HACL_HOME)/lib/fst -I $(KREMLIN_HOME)/kremlib -I $(HACL_HOME)/specs -I . -ccopt '-march=native' -fbuiltin-uint128 -drop FStar.UInt128 -fnocompound-literals -fc89-scope -fparentheses -fcurly-braces
poly64-c/out.krml: $(POLY1305_64_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir poly64-c $(POLY1305_64_FILES) -skip-translation 

poly64-c/Hacl_Poly1305_64.c: poly64-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir poly64-c  $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -add-include '"vec128.h"' -bundle 'Hacl.Poly1305_64=*'

poly1305_64.exe: poly64-c/Hacl_Poly1305_64.c poly64-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir poly64-c \
	  -no-prefix 'Hacl.Test.Poly1305_64' -minimal -add-include '"kremlib.h"' -add-include '"vec128.h"'\
	  -bundle 'Hacl.Test.Poly1305_64=*' -library Hacl.Poly1305_64 -library Lib.Vec128 \
	  $^ -o $@

POLY1305_32_FILES= $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/fst/Lib.RawIntTypes.fst \
	Lib.Utils.fst \
	Hacl.Impl.Poly1305.Field32.fst \
	Hacl.Impl.Poly1305.Fields.fst \
	Hacl.Impl.Poly1305.fst \
	Hacl.Poly1305_32.fst \
	Hacl.Test.Poly1305_32.fst 

poly32-c/out.krml: $(POLY1305_32_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir poly32-c $(POLY1305_32_FILES) -skip-translation 

poly32-c/Hacl_Poly1305_32.c: poly32-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir poly32-c  $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -add-include '"vec128.h"' -bundle 'Hacl.Poly1305_32=*'

poly1305_32.exe: poly32-c/Hacl_Poly1305_32.c poly32-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir poly32-c \
	  -no-prefix 'Hacl.Test.Poly1305_32' -minimal -add-include '"kremlib.h"' -add-include '"vec128.h"'\
	  -bundle 'Hacl.Test.Poly1305_32=*' -library Hacl.Poly1305_32 -library Lib.Vec128 \
	  $^ -o $@

POLY1305_128_FILES= $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/fst/Lib.RawIntTypes.fst \
	Lib.Utils.fst \
	Lib.Vec128.fsti \
	Hacl.Impl.Poly1305.Field128.fst \
	Hacl.Impl.Poly1305.Fields.fst \
	Hacl.Impl.Poly1305.fst \
	Hacl.Poly1305_128.fst \
	Hacl.Test.Poly1305_128.fst 

poly128-c/out.krml: $(POLY1305_128_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir poly128-c $(POLY1305_128_FILES) -skip-translation 

poly128-c/Hacl_Poly1305_128.c: poly128-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir poly128-c  $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -add-include '"vec128.h"' -bundle 'Hacl.Poly1305_128=*'

poly1305_128.exe: poly128-c/Hacl_Poly1305_128.c poly128-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir poly128-c \
	  -no-prefix 'Hacl.Test.Poly1305_128' -minimal -add-include '"kremlib.h"' -add-include '"vec128.h"'\
	  -bundle 'Hacl.Test.Poly1305_128=*' -library Hacl.Poly1305_128 -library Lib.Vec128 \
	  $^ -o $@


POLY1305_256_FILES= $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/fst/Lib.RawIntTypes.fst \
	Lib.Utils.fst \
	Lib.Vec256.fsti \
	Hacl.Impl.Poly1305.Field256.fst \
	Hacl.Impl.Poly1305.Fields.fst \
	Hacl.Impl.Poly1305.fst \
	Hacl.Poly1305_256.fst \
	Hacl.Test.Poly1305_256.fst 

poly256-c/out.krml: $(POLY1305_256_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir poly256-c $(POLY1305_256_FILES) -skip-translation 

poly256-c/Hacl_Poly1305_256.c: poly256-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir poly256-c  $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -add-include '"vec256.h"' -bundle 'Hacl.Poly1305_256=*'

poly1305_256.exe: poly256-c/Hacl_Poly1305_256.c poly256-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir poly256-c \
	  -no-prefix 'Hacl.Test.Poly1305_256' -minimal -add-include '"kremlib.h"' -add-include '"vec256.h"'\
	  -bundle 'Hacl.Test.Poly1305_256=*' -library Hacl.Poly1305_256 -library Lib.Vec256 \
	  $^ -o $@

poly1305-test: poly1305_64.exe poly1305_32.exe poly1305_128.exe  poly1305_256.exe 
	./poly1305_64.exe
	./poly1305_32.exe
	./poly1305_128.exe
	./poly1305_256.exe

poly1305-perf: poly1305_64.exe poly1305_32.exe poly1305_128.exe poly1305_256.exe
	gcc-8 -march=native -mtune=native -Ofast -flto -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . poly64-c/Hacl_Poly1305_64.c poly32-c/Hacl_Poly1305_32.c poly128-c/Hacl_Poly1305_128.c  poly256-c/Hacl_Poly1305_256.c $(KREMLIN_HOME)/kremlib/c/testlib.o poly1305_test.c -o poly1305-perf.exe 
	./poly1305-perf.exe



CHACHA20_FILES= $(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/fst/Lib.RawIntTypes.fst \
	Lib.Utils.fst \
	Lib.Vec256.fsti \
	Hacl.Impl.Chacha20.Core32.fst \
	Hacl.Impl.Chacha20.fst \
	Hacl.Chacha20.fst 

chacha20-c/out.krml: $(CHACHA20_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha20-c $(CHACHA20_FILES) -skip-translation 

chacha20-c/Hacl_Chacha20.c: chacha20-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) -tmpdir chacha20-c  $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -add-include '"vec256.h"' -bundle 'Hacl.Chacha20=*'

chacha20.exe: chacha20-c/Hacl_Chacha20.c chacha20-c/out.krml
	gcc-8 -march=native -mtune=native -Ofast -flto -I $(KREMLIN_HOME)/kremlib/c -I $(KREMLIN_HOME)/include -I . chacha20-c/Hacl_Chacha20.c $(KREMLIN_HOME)/kremlib/c/testlib.o chacha20_test.c -o chacha20.exe 
	./chacha20.exe

chacha20-perf: chacha20.exe


all: aes-bitslice.exe aes-ni.exe gf128ni.exe


count-line:
	cloc --force-lang=ocaml $(AES_FILES)

clean:
	rm -rf *.exe *.exe.* *.out *~ aescbc-c aesni-c gf128ni-c *.graph
