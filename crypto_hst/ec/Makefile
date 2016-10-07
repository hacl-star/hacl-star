FSTAR_HOME?=../../../FStar
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_DEFAULT_ARGS) # from the included Makefile

LIB_DIR=../../lib/hst

OPTIONS_VER=--include $(LIB_DIR) --use_hints

LIB_FILES=Hacl.Cast.fst Hacl.SBuffer.fst Hacl.UInt128.fst Hacl.UInt64.fst Hacl.UInt32.fst Hacl.UInt8.fst

all: curve25519

import-lib:
	@cp $(addprefix ../../lib/hst/, $(LIB_FILES)) .

curve25519: $(addsuffix -ver, \
			Hacl.EC.Curve25519.Bigint.fst \
			Hacl.EC.Curve25519.Bignum.Fsum.fst \
			Hacl.EC.Curve25519.Bignum.FsumWide.fst \
			Hacl.EC.Curve25519.Bignum.Fdifference.fst \
			Hacl.EC.Curve25519.Bignum.Fscalar.fst \
			Hacl.EC.Curve25519.Bignum.Fproduct.fst \
			Hacl.EC.Curve25519.Bignum.Modulo.fst \
			Hacl.EC.Curve25519.Bignum.fst \
			Hacl.EC.Curve25519.PPoint.fst \
			Hacl.EC.Curve25519.AddAndDouble.fst \
			Hacl.EC.Curve25519.Ladder.fst \
			Hacl.EC.Curve25519.Crecip.fst \
			Hacl.EC.Curve25519.Ladder.fst \
			Hacl.EC.Curve25519.fst)

%-ver: %
	$(FSTAR) $(OPTIONS_VER) $^

clean:
	rm -f *~ $(addprefix ml/, *.cmo *.cmi *.o *~ *.cmx) $(LIB_FILES)
