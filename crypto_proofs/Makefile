FSTAR_HOME?=../../FStar

MEM=HST

include $(FSTAR_HOME)/src/gmake/fstar.mk
include $(FSTAR_HOME)/ulib/ml/Makefile.include

FSTAR_ARGS=$(OTHERFLAGS)

KREMLIN_HOME?=~/dev/kremlin

# OCaml variables
OCAMLOPT := $(OCAMLOPT) -w -8-20-26-28-10

FSTAR_EXTRACT=$(FSTAR) $(CODEGEN_ARGS) --include $(FSTAR_HOME)/ulib/hyperstack --include crypto --include crypto/real

KRML_INCLUDES=$(addprefix -I ,test/spartan_aes aead uf1cma primitives prf utils ../code/bignum ../code/poly1305 ../code/salsa-family ../code/lib/kremlin $(KREMLIN_HOME)/kremlib $(KREMLIN_HOME)/test)
KRML_ARGS=-ccopt -maes -ccopt -Wno-error=pointer-sign $(KOPTS) -ccopt -std=gnu99
KRML=$(KREMLIN_HOME)/krml $(KRML_ARGS) $(KRML_INCLUDES) 

test/spartan_aes/aes.o:
	make -C test/spartan_aes

krml-test.exe: test/spartan_aes/aes.o
	$(KRML) utils/Crypto.Config.fst test/Flag.fst utils/Hacl.Spec.fst \
		test/spartan_dummy.c  \
	       	test/Crypto.KrmlTest.fst -no-prefix Crypto.KrmlTest \
	       	$(KREMLIN_HOME)/test/../kremlib/testlib.c test/test_hacks.c \
		-tmpdir tmp -add-include '"testlib.h"' -o krml-test.exe \
		-bundle Hacl.Bignum.* -bundle Hacl.Impl.* \
		-bundle Hacl.Spec=Hacl.Spec.*,Hacl.Spe.* -drop Hacl.Spec
	./krml-test.exe

run-krml-test.exe: 
	gcc-6 -Wno-unused-but-set-variable -std=c11 -Wall -Werror -Wno-parentheses -Wno-unused-variable -g -O3 -fwrapv -I FSTAR_HOME/ulib/hyperstack -I spartan_aes -I crypto -I ../../../kremlin/kremlib -I ../../../kremlin/test -I /Users/bhargava/Desktop/repositories/kremlin/kremlib -I tmp -maes -Wno-error=pointer-sign tmp/Prims.c tmp/Buffer_Utils.c tmp/Crypto_Symmetric_Bytes.c tmp/Crypto_Symmetric_Poly1305_Spec.c tmp/Crypto_Symmetric_Poly1305_Parameters.c tmp/Crypto_Symmetric_Poly1305_Bigint.c tmp/Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part1.c tmp/Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part2.c tmp/Crypto_AEAD_BufferUtils.c tmp/Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part3.c tmp/Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part4.c tmp/Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part5.c tmp/FStar.c tmp/Crypto_Symmetric_Chacha20.c tmp/Crypto_Config.c tmp/Crypto_Indexing.c tmp/Flag.c tmp/Crypto_Symmetric_AES.c tmp/Spartan.c tmp/Crypto_Symmetric_AES128.c tmp/Crypto_Symmetric_Cipher.c tmp/Crypto_Symmetric_Poly1305_Lemmas.c tmp/Crypto_Symmetric_Poly1305_Bignum_Lemmas_Part6.c tmp/Crypto_Symmetric_Poly1305_Bignum.c tmp/Crypto_Symmetric_Poly1305.c tmp/Crypto_Symmetric_GF128_Spec.c tmp/Crypto_Symmetric_GF128.c tmp/Crypto_Symmetric_MAC.c tmp/Crypto_Symmetric_UF1CMA.c tmp/Crypto_Plain.c tmp/Crypto_Symmetric_PRF.c tmp/Crypto_AEAD_Encoding.c tmp/Crypto_AEAD_Invariant.c tmp/Crypto_AEAD_Wrappers_Encoding.c tmp/Crypto_AEAD_Wrappers_CMA.c tmp/Crypto_AEAD_Encrypt_Invariant.c tmp/Crypto_AEAD_Wrappers_PRF.c tmp/Crypto_AEAD_EnxorDexor.c tmp/Crypto_AEAD_Encrypt_Ideal_Invariant.c tmp/Crypto_AEAD_MAC_Wrapper_Invariant.c tmp/Crypto_AEAD_Enxor_Invariant.c tmp/Crypto_AEAD_Encrypt.c tmp/Crypto_AEAD_Decrypt.c tmp/Crypto_AEAD.c tmp/Crypto_KrmlTest.c tmp/kremlib.o test/test_hacks.c tmp/testlib.o tmp/spartan_stub.o spartan_aes/aes.o -o krml-test.exe

OPENSSL_HOME=$(FSTAR_HOME)/ucontrib/CoreCrypto/ml/openssl
#OPENSSL_HOME=/usr/local/Cellar/openssl\@1.1/1.1.0c
CC=gcc-6 

test-perf.exe: krml-test.exe test/test_perf.c
	$(CC) -Ofast -m64 -flto -march=native -mtune=native -funroll-loops -fomit-frame-pointer \
	 -o test-perf.exe tmp/FStar.c tmp/Crypto_AEAD*.c tmp/Crypto_Indexing*.c tmp/Crypto_Symmetric*.c tmp/Hacl_Impl*.c tmp/Hacl_Bignum*.c tmp/Hacl_Symmetric_Chacha20.c tmp/Buffer_Utils*.c tmp/Crypto_Plain*.c $(KREMLIN_HOME)/kremlib/kremlib.c \
		$(KREMLIN_HOME)/test/../kremlib/testlib.c test/test_perf.c test/spartan_dummy.c test/test_hacks.c  -I tmp  \
		-I $(KREMLIN_HOME)/kremlib -I $(KREMLIN_HOME)/test \
		-I $(OPENSSL_HOME)/include -L $(OPENSSL_HOME) -lcrypto $(CFLAGS)
	PATH=$(OPENSSL_HOME):$(PATH) LD_LIBRARY_PATH=$(OPENSSL_HOME):$(LD_LIBRARY_PATH) DYLD_LIBRARY_PATH=$(OPENSSL_HOME):$(DYLD_LIBRARY_PATH) ./test-perf.exe

# Cleaning
clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	@rm -f $(addprefix crypto/ml/, *.cmx *.o *.cmi *~)
	@rm -rf tmp kremlin *~ *.exe

KREMLIN_HOME=$(FSTAR_HOME)/../kremlin

FSTAR?=$(FSTAR_HOME)/bin/fstar.exe

HINTS_ENABLED?=--use_hints

OPTIONS=--fstar_home $(FSTAR_HOME) --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 0 --z3rlimit 20  $(HINTS_ENABLED) $(OTHERFLAGS)

FSTAR_INCLUDE_PATHS=--include $(FSTAR_HOME)/ulib/hyperstack --include utils --include primitives --include prf --include uf1cma --include aead --include ../code/bignum --include ../code/poly1305 --include ../code/salsa-family --include ../code/lib/kremlin --include $(KREMLIN_HOME)/kremlib/

VERIFY= \
  utils/Buffer.Utils \
  utils/Crypto.Symmetric.Bytes \
  primitives/Crypto.Symmetric.GF128 \
  primitives/Crypto.Symmetric.AES \
  primitives/Crypto.Symmetric.AES128 \
  prf/Crypto.Symmetric.Cipher \
  prf/Crypto.Symmetric.PRF \
  uf1cma/Crypto.Symmetric.MAC \
  uf1cma/Crypto.Symmetric.UF1CMA \
  aead/Crypto.AEAD.Encrypt.Invariant \
  aead/Crypto.AEAD.Encoding \
  aead/Crypto.AEAD.Invariant \
  aead/Crypto.AEAD.BufferUtils \
  aead/Crypto.AEAD.Enxor.Invariant \
  aead/Crypto.AEAD.Wrappers.CMA \
  aead/Crypto.AEAD.Wrappers.Encoding \
  aead/Crypto.AEAD.EnxorDexor \
  aead/Crypto.AEAD.Wrappers.PRF \
  aead/Crypto.AEAD.Decrypt \
  aead/Crypto.AEAD.MAC_Wrapper.Invariant \
  aead/Crypto.AEAD.Encrypt.Ideal.Invariant \
  aead/Crypto.AEAD.Encrypt \
  aead/Crypto.AEAD \
  aead/Crypto.Plain

#  Crypto.Symmetric.Poly1305.Lemmas  # verification target is not passing reliably so commenting out

#16-10-30 removed files specific to Poly1305:
#  Crypto.Symmetric.Poly1305.MAC 
#  Crypto.AEAD.Chacha20Poly1305


# Files that should fully typecheck, but not part of regression
# because verification is too slow
SLOW= \

# Files not yet fully typechecking -- possibly due to timeouts.
# Please move files that you know fully typecheck to VERIFY
# Files commented out are broken, uncomment once fixed
LAX=

# \
#   Crypto.Symmetric.Poly1305 \
#   Crypto.AEAD #NS: both of these verify, but each takes 20+ mins to verify


#16-10-09  Not sure how to verify Flag.fsti and Flag.fst

all: all-ver $(addsuffix .fst-lax, $(LAX))

extra: all-ver $(addsuffix .fst-ver, $(EXTRA))

all-ver: $(addsuffix .fst-ver, $(VERIFY))

all-hints: $(addsuffix .fst-hints, $(VERIFY))

all-lax: $(addsuffix .fst-lax, $(LAX)) $(addsuffix .fst-lax, $(VERIFY))

# Parameter for interactive mode
%.fst-in: 
	@echo $(OPTIONS) \
	$(FSTAR_INCLUDE_PATHS) \
	--__temp_no_proj Crypto.Symmetric.MAC \
	--verify_module $(basename $(notdir $@))

# Verifying one file at a time
%.fst-ver:
	$(FSTAR) $(OPTIONS) \
	$(FSTAR_INCLUDE_PATHS) \
	--__temp_no_proj Crypto.Symmetric.MAC \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst

# (Re-)Generate hints
%.fst-hints:
	$(FSTAR) $(OPTIONS) --record_hints \
	$(FSTAR_INCLUDE_PATHS) \
	--__temp_no_proj Crypto.Symmetric.MAC \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst

# Lax verifying one file at a time
%.fst-lax:
	$(FSTAR) $(OPTIONS) \
	$(FSTAR_INCLUDE_PATHS) --lax \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst

AEAD_FILES=$(addsuffix .fst, $(VERIFY))
aead-ver: $(addsuffix -ver, $(AEAD_FILES))

aead-wc:
	wc -l $(AEAD_FILES)

all-assumes: $(addsuffix .fst, $(VERIFY) $(LAX))
	grep "\(assume\)\|\(admit\)\|\(lax\)" $^
