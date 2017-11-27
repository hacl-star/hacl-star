all: verify

hints:
	$(FSTAR_HOME)/bin/fstar.exe fst/Spec.Lib.IntTypes.fst --record_hints 
	$(FSTAR_HOME)/bin/fstar.exe fst/Spec.Lib.IntTypes.fst fst/Spec.Lib.RawIntTypes.fst --record_hints
	$(FSTAR_HOME)/bin/fstar.exe fst/Spec.Lib.IntSeq.fst --record_hints
	$(FSTAR_HOME)/bin/fstar.exe fst/Spec.Lib.IntVec.fst --record_hints 
	$(FSTAR_HOME)/bin/fstar.exe fst/Spec.Lib.Stateful.fst --record_hints
	$(FSTAR_HOME)/bin/fstar.exe fst/Spec.Lib.Stateful2.fst --record_hints
	$(FSTAR_HOME)/bin/fstar.exe fst/Spec.Lib.IntTypes.fst fst/Spec.Lib.RawIntTypes.fst fst/Spec.Lib.IntSeq.fst fst/Spec.Lib.IntVec.fst fst/Spec.Lib.Stateful.fst

verify:
	$(FSTAR_HOME)/bin/fstar.exe fst/Spec.Lib.IntTypes.fst --use_hints 
	$(FSTAR_HOME)/bin/fstar.exe fst/Spec.Lib.IntTypes.fst fst/Spec.Lib.RawIntTypes.fst --use_hints
	$(FSTAR_HOME)/bin/fstar.exe fst/Spec.Lib.IntSeq.fst --use_hints
	$(FSTAR_HOME)/bin/fstar.exe fst/Spec.Lib.IntVec.fst --use_hints 
	$(FSTAR_HOME)/bin/fstar.exe fst/Spec.Lib.Stateful.fst --use_hints
	$(FSTAR_HOME)/bin/fstar.exe fst/Spec.Lib.Stateful2.fst --record_hints
	$(FSTAR_HOME)/bin/fstar.exe fst/Spec.Lib.IntTypes.fst fst/Spec.Lib.RawIntTypes.fst fst/Spec.Lib.IntSeq.fst fst/Spec.Lib.IntVec.fst fst/Spec.Lib.Stateful.fst

