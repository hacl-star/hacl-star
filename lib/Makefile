all: verify

hints:
	$(FSTAR_HOME)/bin/fstar.exe fst/Lib.IntTypes.fst --record_hints 
	$(FSTAR_HOME)/bin/fstar.exe fst/Lib.IntTypes.fst fst/Lib.RawIntTypes.fst --record_hints
	$(FSTAR_HOME)/bin/fstar.exe fst/Lib.IntSeq.fst --record_hints
	$(FSTAR_HOME)/bin/fstar.exe fst/Lib.IntVec.fst --record_hints 
	$(FSTAR_HOME)/bin/fstar.exe fst/Lib.Stateful.fst --record_hints
	$(FSTAR_HOME)/bin/fstar.exe fst/Lib.Stateful2.fst --record_hints
	$(FSTAR_HOME)/bin/fstar.exe fst/Lib.IntTypes.fst fst/Lib.RawIntTypes.fst fst/Lib.IntSeq.fst fst/Lib.IntVec.fst fst/Lib.Stateful.fst

verify:
	$(FSTAR_HOME)/bin/fstar.exe fst/Lib.IntTypes.fst --use_hints 
	$(FSTAR_HOME)/bin/fstar.exe fst/Lib.IntTypes.fst fst/Lib.RawIntTypes.fst --use_hints
	$(FSTAR_HOME)/bin/fstar.exe fst/Lib.IntSeq.fst --use_hints
	$(FSTAR_HOME)/bin/fstar.exe fst/Lib.IntVec.fst --use_hints 
	$(FSTAR_HOME)/bin/fstar.exe fst/Lib.Stateful.fst --use_hints
	$(FSTAR_HOME)/bin/fstar.exe fst/Lib.Stateful2.fst --record_hints
	$(FSTAR_HOME)/bin/fstar.exe fst/Lib.IntTypes.fst fst/Lib.RawIntTypes.fst fst/Lib.IntSeq.fst fst/Lib.IntVec.fst fst/Lib.Stateful.fst

