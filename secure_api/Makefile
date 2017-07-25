include ../code/Makefile.include

OPENSSL_HOME=$(FSTAR_HOME)/ucontrib/CoreCrypto/ml/openssl

#17-02-13 in low-level, we used to have two Makefiles, merged here.
MEM=HST

ifeq ($(OS),Windows_NT)
  FPIC =
else
  ifeq ($(UNAME),Darwin)
    FPIC =
  else
    FPIC = -ccopt -fPIC
  endif
endif

LDEPS=aead uf1cma vale vale/asm prf hkdf utils indexing
CDEPS=experimental/aesgcm bignum poly1305 salsa-family hash

KREMLIN_ARGS+=$(addprefix -I ,$(LDEPS)) \
	$(addprefix -I $(HACL_HOME)/code/,$(CDEPS)) \
	-I $(KREMLIN_HOME)/test

KREMLIN_ARGS+=$(FPIC) -ccopt -maes -fnouint128 \
  test/test_hacks.c \
  -drop Hacl.Spe.*,Spec,Hacl.Spec,Spec.*,Hacl.Spec.* \
  $(KREMLIN_TESTLIB) \
  -bundle Hacl.* $(KOPTS)

# JP: is this rule temporary?
LowCProvider-tmp: vale/asm/vale.a
	$(KREMLIN) $(KREMLIN_ARGS) LowCProvider/Crypto.Indexing.fst \
		test/Flag.fst utils/Hacl.Spec.fst \
		aead/Crypto.AEAD.fst \
		-tmpdir LowCProvider/tmp \
		-skip-linking

QuicProvider-tmp: vale/asm/vale.a
	$(KREMLIN) $(KREMLIN_ARGS) LowCProvider/Crypto.Indexing.fst \
		test/Flag.fst utils/Hacl.Spec.fst \
		aead/Crypto.AEAD.fst hkdf/Crypto.HKDF.fst \
		-tmpdir QuicProvider/tmp \
		-skip-linking

tmp-%/out.krml: $(wildcard */*.fst)
	$(KREMLIN) $(KREMLIN_ARGS) test/test_$*/Crypto.Indexing.fst \
	  test/Flag.fst utils/Hacl.Spec.fst \
	  test/Crypto.KrmlTest.fst \
	  -tmpdir tmp-$* -skip-translation

ifndef USE_CL # Wintersteiger: Vale doesn't build with Visual Studio.
vale/asm/vale.a:
	$(MAKE) -C vale/asm

krml-test-vale.exe: tmp-vale/out.krml vale/asm/vale.a
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir tmp-vale $^ -o $@ -bundle "Crypto.AEAD=Crypto.AEAD.*" -no-prefix Crypto.KrmlTest
	./$@
else
krml-test-vale.exe:

krml-test-hacl.exe: tmp-hacl/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -tmpdir tmp-hacl $^ -o $@ -bundle "Crypto.AEAD=Crypto.AEAD.*" -no-prefix Crypto.KrmlTest
	./$@
endif

test-perf-hacl.exe: krml-test-hacl.exe test/test_perf.c
	$(CC) -Ofast -m64 -march=native -mtune=native -funroll-loops -fomit-frame-pointer -o $@ \
		tmp-hacl/Crypto_AEAD*.c tmp-hacl/Crypto_Indexing*.c tmp-hacl/Buffer_Utils*.c \
		-I $(KREMLIN_HOME)/kremlib -I $(KREMLIN_HOME)/test \
		-I $(OPENSSL_HOME)/include -L $(OPENSSL_HOME) -lcrypto $(CFLAGS) \
		$(KREMLIN_HOME)/kremlib/kremlib.c $(KREMLIN_HOME)/kremlib/testlib.c \
		test/test_perf.c test/test_hacks.c -I tmp-hacl
	PATH="$(OPENSSL_HOME):$(PATH)" LD_LIBRARY_PATH="$(OPENSSL_HOME):$(LD_LIBRARY_PATH)" DYLD_LIBRARY_PATH="$(OPENSSL_HOME):$(DYLD_LIBRARY_PATH)" ./$@

# Cleaning
clean:
	$(MAKE) -C LowCProvider clean
	$(MAKE) -C vale/asm clean
	@rm -f $(addprefix crypto/ml/, *.cmx *.o *.cmi *~)
	@rm -rf tmp tmp-vale tmp-hacl kremlin *~ *.exe

OTHERFLAGS+=--max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 0 --z3rlimit 20

OTHERFLAGS+=$(addprefix --include ,$(LDEPS)) \
	$(addprefix --include $(HACL_HOME)/code/,$(CDEPS)) \
	--include $(KREMLIN_HOME)/test

# TODO integrate GF128 with specs and code
# TODO recheck why we dropped TestMonotonic and AES256GCM
# TODO store our old 32-bit Poly1305 verified code (by default keep in auxiliary directory)

# TODO document (or even call) auxiliary verification targets elsewhere!
# for example it is unclear where and how to reverify the libraries and Poly1305.

# Files that should fully typecheck
# Files commented out are broken, uncomment once fixed
VERIFY= \
  utils/Buffer.Utils \
  utils/Crypto.Symmetric.Bytes \
  ../code/experimental/aesgcm/Crypto.Symmetric.GF128 \
  ../code/experimental/aesgcm/Crypto.Symmetric.AES \
  ../code/experimental/aesgcm/Crypto.Symmetric.AES128 \
  prf/Crypto.Symmetric.Cipher \
  prf/Crypto.Symmetric.PRF \
  uf1cma/Crypto.Symmetric.MAC \
  uf1cma/Crypto.Symmetric.UF1CMA \
  aead/Crypto.AEAD.Encoding \
  aead/Crypto.AEAD.Invariant \
  aead/Crypto.AEAD.BufferUtils \
  aead/Crypto.AEAD.Encrypt.Invariant \
  aead/Crypto.AEAD.Enxor.Invariant \
  aead/Crypto.AEAD.EnxorDexor \
  aead/Crypto.AEAD.Wrappers.PRF \
  aead/Crypto.AEAD.Wrappers.CMA \
  aead/Crypto.AEAD.Wrappers.Encoding \
  aead/Crypto.AEAD.Decrypt \
  aead/Crypto.AEAD.MAC_Wrapper.Invariant \
  aead/Crypto.AEAD.Encrypt.Ideal.Invariant \
  aead/Crypto.AEAD.Encrypt \
  aead/Crypto.AEAD \
  aead/Crypto.Plain

EXTRA= \
  Crypto.Symmetric.Poly1305 \
  Crypto.Test
# TODO Crypto.Test has moved; probably call test/KrmlTest instead.

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

verify: $(addsuffix .fst-ver, $(filter-out $(LAX), $(VERIFY)))
hints: $(addsuffix .fst.hints, $(VERIFY))
lax: $(addsuffix .fst-lax, $(LAX)) $(addsuffix .fst-lax, $(VERIFY))

all-hints: hints
all-ver: verify
all-lax: lax


# Parameter for interactive mode
%.fst-in:
	@echo --hint_info \
	$(HINTS_ENABLED) \
	$(OTHERFLAGS) \
	$(FSTAR_INCLUDES)

%.fsti-in:
	@echo --hint_info \
	$(FSTAR_INCLUDES)

# Verifying one file at a time
%.fst-ver:
	$(FSTAR) \
	--__temp_no_proj Crypto.Symmetric.MAC \
	$(basename $@).fst

# (Re-)Generate hints
%.fst.hints:
	$(FSTAR) --record_hints \
	--__temp_no_proj Crypto.Symmetric.MAC \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst

# Lax verifying one file at a time
%.fst-lax:
	$(FSTAR) --lax \
	--verify_module $(basename $(notdir $@)) \
	$(basename $@).fst

AEAD_FILES=$(addsuffix .fst, $(VERIFY))
aead-ver: $(addsuffix -ver, $(AEAD_FILES))

aead-wc:
	wc -l $(AEAD_FILES)

all-assumes: $(addsuffix .fst, $(VERIFY) $(LAX))
	grep "\(assume\)\|\(admit\)\|\(lax\)" $^
