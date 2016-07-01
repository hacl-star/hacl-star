# FStar variables
FSTAR_HOME?=../../../FStar
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_DEFAULT_ARGS) # from the included Makefile

OPTIONS_VER=

LIB_DIR=../../lib/st/
TEST_DIR=../../test/ec

LIB_FILES=$(addprefix $(LIB_DIR), axioms.fst intlib.fst IntLibLemmas.fst sint.fst sbuffer.fst SInt.UInt8.fst SInt.UInt32.fst SInt.UInt63.fst SInt.UInt64.fst SInt.Cast.fst SBytes.fst)

.PHONY: lib-ver chacha-ver chacha-ml poly-ver poly-ml

all: lib-ver chacha-ver poly-ver

# Verification target for the low-level libraries of F* in universes
lib-ver:
	$(FSTAR) $(OPTIONS_VER) $(LIB_FILES)

# Verification target for CHACHA20
chacha-ver: 
	$(FSTAR) $(OPTIONS_VER) $(LIB_FILES) chacha.fst

# Verification target for POLY1305
poly-ver:
	$(FSTAR) $(OPTIONS_VER) $(LIB_FILES) parameters.fst bigint.fst bignum.fst poly.fst

# AES targets
aes-ver:
	$(FSTAR) $(OPTIONS_VER) $(LIB_FILES) Crypto.AES.fst --lax

# AEAD targets
aead-ver:
	$(FSTAR) $(OPTIONS_VER) $(LIB_FILES) chacha.fst parameters.fst bigint.fst bignum.fst poly.fst --lax AEAD.ChaCha20_Poly1305.fst

# Cleaning
clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	@rm -f $(addprefix ml/, *.cmx *.o *.cmi *~)
	@rm -rf $(CHACHA_ODIR) $(POLY_ODIR) $(CHACHA_ODIR)_ml $(POLY_ODIR)_ml \
		$(BIGNUM_ODIR) $(CURVE_ODIR) $(AES_ODIR) *~ *.exe
