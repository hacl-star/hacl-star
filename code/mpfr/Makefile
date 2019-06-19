# For simplified Makefiles, define FSTAR_HOME, then include the file below.
include ../../Makefile.include

#You shoukd set FSTAR_HOME and KREMLIN_HOME to where you cloned those two repos
#Usually it is better to define these environment variables in the .bash_profile
FSTAR_HOME=/home/felix/FStar
KREMLIN_HOME=~/kremlin

FSTAR=$(FSTAR_HOME)/bin/fstar.exe

all: test-ocaml

MPFR_FILES=	MPFR.Maths.fst \
		MPFR.Dyadic.fst \
		MPFR.Lib.Spec.fst \
		MPFR.Add1.Spec.fst \
		MPFR.RoundingMode.fst \
		MPFR.Round.Spec.fst \
		MPFR.Lib.fst \
		MPFR.Exceptions.Lemma.fst \
		MPFR.Exceptions.fst \
		MPFR.Add1sp1.Lemma.fst \
		MPFR.Add1sp1.fst \
		MPFR.Umul_ppmm.fst \
		MPFR.Mul.Spec.fst \
		MPFR.Mul_1.fst \
		MPFR.fst\
		Test.MPFR.fst

# This target is very concise and re-uses the variables defined in
# Makefile.include. You shouldn't need to call `cp` ever.

#add1sp1-full-tests: out gen-add1sp1-tests MPFR.RoundingMode.fst MPFR.Lib.fst MPFR.Exceptions.fst MPFR.Add1sp1.fst test/Test_Add1sp1.ml
#	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --lax --odir out --codegen OCaml MPFR.Add1sp1.fst
#	cp test/Test_Add1sp1.ml out/Test_Add1sp1.ml
#	$(OCAMLOPT) -I $(FSTAR_HOME)/ulib/ml -I out out/MPFR_RoundingMode.ml out/MPFR_Lib.ml out/MPFR_Exceptions.ml out/MPFR_Add1sp1.ml out/Test_Add1sp1.ml -o out/Add1sp1
#	out/Add1sp1

#mul-1-full-tests: out gen-mul-1-tests MPFR.RoundingMode.fst MPFR.Lib.fst MPFR.Exceptions.fst MPFR.Umul_ppmm.fst MPFR.Mul_1.fst test/Test_Mul_1.ml
#	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --lax --odir out --codegen OCaml MPFR.Mul_1.fst
#	cp test/Test_Mul_1.ml out/Test_Mul_1.ml
#	$(OCAMLOPT) -I $(FSTAR_HOME)/ulib/ml -I out out/MPFR_RoundingMode.ml out/MPFR_Lib.ml out/MPFR_Exceptions.ml out/MPFR_Umul_ppmm.ml out/MPFR_Mul_1.ml out/Test_Mul_1.ml -o out/Mul_1
#	out/Mul_1

test-ocaml: out MPFR.RoundingMode.fst MPFR.Lib.fst MPFR.Exceptions.fst MPFR.Add1sp1.fst MPFR.Umul_ppmm.fst MPFR.Mul_1.fst MPFR.fst Test.MPFR.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --lax --odir out --codegen OCaml Test.MPFR.fst
	echo "let _ = main ()" >> out/Test_MPFR.ml
	$(OCAMLOPT) -I $(FSTAR_HOME)/ulib/ml -I out out/MPFR_RoundingMode.ml out/MPFR_Lib.ml out/MPFR_Exceptions.ml out/MPFR_Add1sp1.ml out/MPFR_Umul_ppmm.ml out/MPFR_Mul_1.ml out/MPFR.ml out/Test_MPFR.ml -o out/Test_MPFR
	out/Test_MPFR

%.fst-verify: %.fst
	$(FSTAR) --include $(KREMLIN_HOME)/kremlib --use_hints --cache_checked_modules $*.fst

%.fst-hints: %.fst
	$(FSTAR) --z3rlimit_factor 5 --use_hints --record_hints $*.fst

%.fst-reg-hints: %.fst
	$(FSTAR) --z3rlimit_factor 5 --record_hints $*.fst

verify: $(addsuffix -verify, $(MPFR_FILES))
hints: $(addsuffix -hints, $(MPFR_FILES))
reg-hints: $(addsuffix -reg-hints, $(MPFR_FILES))

out:
	mkdir -p out

#gen-add1sp1-tests: test/gen.c test/tadd_raw
#	cc -o test/gen test/gen.c -lmpfr -lgmp
#	test/gen test/tadd_raw test/add1sp1_tests
#	rm test/gen

#gen-mul-1-tests: test/gen.c test/tmul_raw
#	cc -o test/gen test/gen.c -lmpfr -lgmp
#	test/gen test/tmul_raw test/mul_1_tests
#	rm test/gen

#gen-tests: gen-add1sp1-tests gen-mul-1-tests


KREMLIN_ARGS+=-tmpdir mpfr-c 

mpfr-c/out.krml: $(MPFR_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) $(MPFR_FILES) -skip-translation

mpfr-c/MPFR.c: mpfr-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -bundle 'MPFR=*' -fparentheses

extract-c: mpfr-c/MPFR.c

mpfr.exe: mpfr-c/MPFR.c mpfr-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) \
	  -no-prefix 'Test.MPFR' -minimal -add-include '"kremlib.h"' \
	  -bundle 'Test.MPFR=*' -library MPFR \
	  $^ -o $@

test: mpfr.exe
	./$^


clean:
	rm -rf out mpfr-c
	rm -f *~
	rm -f test/*~ 
