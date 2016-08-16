FSTAR_HOME?=../../../FStar
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_DEFAULT_ARGS) # from the included Makefile

OPTIONS_VER=

LIB_FILES=Math.Axioms.fst Math.Lib.fst Math.Lemmas.fst Hacl.SBuffer.fst Hacl.UInt8.fst Hacl.UInt16.fst Hacl.UInt32.fst Hacl.UInt64.fst Hacl.UInt128.fst Hacl.Cast.fst

ver:
	$(FSTAR) $(OPTIONS_VER) $(LIB_FILES)

clean:
	rm -f *~ $(addprefix ml/, *.cmo *.cmi *.o *~ *.cmx)
