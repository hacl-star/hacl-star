FSTAR_HOME?=../../../FStar
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_DEFAULT_ARGS) # from the included Makefile

OPTIONS_VER=

LIB_FILES=Hacl.Cast.fst Hacl.SBuffer.fst Hacl.UInt128.fst Hacl.UInt64.fst Hacl.UInt32.fst Hacl.UInt8.fst Math.Axioms.fst Math.Lib.fst Math.Lemmas.fst

import-lib:
	@cp $(addprefix ../../lib/hst/, $(LIB_FILES)) .

# ver:
# 	$(FSTAR) $(OPTIONS_VER) $(LIB_FILES)

clean:
	rm -f *~ $(addprefix ml/, *.cmo *.cmi *.o *~ *.cmx) $(LIB_FILES)
