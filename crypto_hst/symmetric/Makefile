FSTAR_HOME?=../../../FStar
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe

LIB_DIR=../../lib/hst

OPTIONS_VER=--include $(LIB_DIR) --initial_fuel 0 --max_fuel 0

LIB_FILES=Hacl.Cast.fst Hacl.SBuffer.fst Hacl.UInt128.fst Hacl.UInt64.fst Hacl.UInt32.fst Hacl.UInt8.fst Math.Axioms.fst Math.Lib.fst Math.Lemmas.fst

all: chacha aes

import-lib:
	@cp $(addprefix ../../lib/hst/, $(LIB_FILES)) .

chacha:
	$(FSTAR) $(OPTIONS_VER) Hacl.Symmetric.Chacha20.fst --z3timeout 20

aes:
	$(FSTAR) $(OPTIONS_VER) Hacl.Symmetric.AES.fst --z3timeout 20

clean:
	rm -f *~ $(addprefix ml/, *.cmo *.cmi *.o *~ *.cmx) $(LIB_FILES)
