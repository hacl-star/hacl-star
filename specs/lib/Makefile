all: verify

hints:
	$(FSTAR_HOME)/bin/fstar.exe Spec.Lib.IntTypes.fst --record_hints 
	$(FSTAR_HOME)/bin/fstar.exe Spec.Lib.IntTypes.fst Spec.Lib.RawIntTypes.fst --record_hints
	$(FSTAR_HOME)/bin/fstar.exe Spec.Lib.IntSeq.fst --record_hints
	$(FSTAR_HOME)/bin/fstar.exe Spec.Lib.IntVec.fst --record_hints 
	$(FSTAR_HOME)/bin/fstar.exe Spec.Lib.Stateful.fst --record_hints
	$(FSTAR_HOME)/bin/fstar.exe Spec.Lib.Stateful2.fst --record_hints
	$(FSTAR_HOME)/bin/fstar.exe Spec.Lib.IntTypes.fst Spec.Lib.RawIntTypes.fst Spec.Lib.IntSeq.fst Spec.Lib.IntVec.fst Spec.Lib.Stateful.fst

verify:
	$(FSTAR_HOME)/bin/fstar.exe Spec.Lib.IntTypes.fst --use_hints 
	$(FSTAR_HOME)/bin/fstar.exe Spec.Lib.IntTypes.fst Spec.Lib.RawIntTypes.fst --use_hints
	$(FSTAR_HOME)/bin/fstar.exe Spec.Lib.IntSeq.fst --use_hints
	$(FSTAR_HOME)/bin/fstar.exe Spec.Lib.IntVec.fst --use_hints 
	$(FSTAR_HOME)/bin/fstar.exe Spec.Lib.Stateful.fst --use_hints
	$(FSTAR_HOME)/bin/fstar.exe Spec.Lib.Stateful2.fst --record_hints
	$(FSTAR_HOME)/bin/fstar.exe Spec.Lib.IntTypes.fst Spec.Lib.RawIntTypes.fst Spec.Lib.IntSeq.fst Spec.Lib.IntVec.fst Spec.Lib.Stateful.fst

