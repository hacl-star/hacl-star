FSTAR_HOME=$(HACL_HOME)/../FStar

include ../../Makefile.include

FSTAR_INCLUDES+=--include $(HACL_HOME)/lib --include $(HACL_HOME)/lib/fst --include $(HACL_HOME)/specs/lemmas

Lib.PQ.Buffer.fst-verify: Lib.PQ.Buffer.fst
	$(FSTAR) --cache_checked_modules --expose_interfaces Lib.IntTypes.fst $<

Lib.Buffer.fst-verify: Lib.Buffer.fst
	$(FSTAR) --cache_checked_modules --expose_interfaces Lib.Sequence.fst Lib.IntTypes.fst $<
