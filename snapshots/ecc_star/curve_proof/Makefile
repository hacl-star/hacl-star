# Change to local F* root directory
FSTAR_HOME=~/dev/old_fstar/FStar
FSTAR=$(FSTAR_HOME)/bin/fstar.exe
BIGNUM=../bignum_proof
MATH=../math_interfaces

# Common verification options
VER_OPTIONS=--admit_fsi FStar.Set --admit_fsi Parameters --admit_fsi Modulo --admit_fsi Bignum FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst seq.fsi FStar.Seq.Base.fst FStar.Seq.Properties.fst FStar.Seq.fst FStar.Array.fst FStar.Ghost.fst $(BIGNUM)/axiomatic.fst $(BIGNUM)/intlib.fst $(BIGNUM)/lemmas.fst $(BIGNUM)/parameters.fsti $(BIGNUM)/uint.fst $(BIGNUM)/bigint.fst $(BIGNUM)/eval.fst $(MATH)/definitions.fst $(MATH)/field.fst $(BIGNUM)/modulo.fsti $(BIGNUM)/bignum.fsti $(MATH)/curve.fst

all: ladder point

point: concrete_point.fst
	$(FSTAR) --z3timeout 2000 $(VER_OPTIONS) $^ --verify_module ConcretePoint 

# The double & add fonctional correctness relies on the SAGE script

ladder: montgomery_ladder_lemmas.fst montgomery_ladder.fst
	$(FSTAR) --z3timeout 5000 $(VER_OPTIONS) concrete_point.fst double_and_add.fst $^ --verify_module MontgomeryLadderLemmas --verify_module MontgomeryLadder

clean:
	rm -f *~ ./ml/*~
