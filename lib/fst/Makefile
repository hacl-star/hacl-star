# FSTAR_HOME ?= $(HACL_HOME)/../FStar

include $(HACL_HOME)/Makefile.include

FSTAR_INCLUDES+=--include $(HACL_HOME)/lib --include $(HACL_HOME)/lib/fst --include $(HACL_HOME)/specs/lemmas

Lib.Buffer.fst-verify: Lib.Buffer.fst
	$(FSTAR) --cache_checked_modules $< #--expose_interfaces Lib.IntTypes.fst $<

Lib.RawIntTypes.fst-verify: Lib.RawIntTypes.fst
	$(FSTAR) --cache_checked_modules --expose_interfaces Lib.IntTypes.fst $<

