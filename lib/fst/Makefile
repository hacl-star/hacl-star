FSTAR_HOME=$(HACL_HOME)/../FStar

include ../../Makefile.include

FSTAR_INCLUDES+=--include $(HACL_HOME)/lib --include $(HACL_HOME)/lib/fst --include $(HACL_HOME)/specs/lemmas

Lib.PQ.Buffer.fst-verify: Lib.PQ.Buffer.fst
	$(FSTAR) --expose_interfaces Lib.IntTypes.fst $<
