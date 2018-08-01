# For simplified Makefiles, define FSTAR_HOME, then include the file below.
include ../../Makefile.include

#You shoukd set FSTAR_HOME and KREMLIN_HOME to where you cloned those two repos
#Usually it is better to define these environment variables in the .bash_profile
#FSTAR_HOME=
#KREMLIN_HOME=

FSTAR=$(FSTAR_HOME)/bin/fstar.exe

all: add1sp1

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
		MPFR.fst

# This target is very concise and re-uses the variables defined in
# Makefile.include. You shouldn't need to call `cp` ever.
add1sp1: out gen-tests MPFR.RoundingMode.fst MPFR.Lib.fst MPFR.Exceptions.fst MPFR.Add1sp1.fst test/Test_Add1sp1.ml
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --lax --odir out --codegen OCaml MPFR.Add1sp1.fst
	cp test/Test_Add1sp1.ml out/Test_Add1sp1.ml
	$(OCAMLOPT) -I $(FSTAR_HOME)/ulib/ml -I out out/MPFR_RoundingMode.ml out/MPFR_Lib.ml out/MPFR_Exceptions.ml out/MPFR_Add1sp1.ml out/Test_Add1sp1.ml -o out/Add1sp1
	out/Add1sp1

%.fst-verify: %.fst
	$(FSTAR) --use_hints $*.fst

%.fst-hints: %.fst
	$(FSTAR) --z3rlimit_factor 5 --use_hints --record_hints $*.fst

%.fst-reg-hints: %.fst
	$(FSTAR) --z3rlimit_factor 5 --record_hints $*.fst

verify: $(addsuffix -verify, $(MPFR_FILES))
hints: $(addsuffix -hints, $(MPFR_FILES))
reg-hints: $(addsuffix -reg-hints, $(MPFR_FILES))

out:
	mkdir -p out

gen-tests: test/gen.c test/add1sp_tests
	cc -o test/gen test/gen.c -lmpfr -lgmp
	test/gen
	rm test/gen


KREMLIN_ARGS+=-tmpdir mpfr-c 

mpfr-c/out.krml: $(MPFR_FILES)
	 $(KREMLIN) $(KREMLIN_ARGS) $(MPFR_FILES) -skip-translation

mpfr-c/MPFR.c: mpfr-c/out.krml
	 $(KREMLIN) $(KREMLIN_ARGS) $^ -skip-compilation \
	   -minimal -add-include '"kremlib.h"' -bundle 'MPFR=*'

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
