# For simplified Makefiles, define FSTAR_HOME, then include the file below.
FSTAR_HOME=~/.opam/4.05.0/packages.dev/fstar
FSTAR=fstar.exe

all: add1sp1

include $(FSTAR_HOME)/ulib/ml/Makefile.include

MPFR_FILES=	MPFR.Maths.fst \
		MPFR.Dyadic.fst \
		MPFR.Lib.Spec.fst \
		MPFR.Add1.Spec.fst \
		MPFR.RoundingMode.fst \
		MPFR.Round.Spec.fst \
		MPFR.Lib.fst \
		MPFR.Add1sp1.fst

# This target is very concise and re-uses the variables defined in
# Makefile.include. You shouldn't need to call `cp` ever.
add1sp1: out gen-tests MPFR.RoundingMode.fst MPFR.Lib.fst MPFR.Add1sp1.fst test/Test_Add1sp1.ml
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --lax --odir out --codegen OCaml MPFR.Add1sp1.fst
	cp test/Test_Add1sp1.ml out/Test_Add1sp1.ml
	$(OCAMLOPT) -I $(FSTAR_HOME)/ulib/ml -I out out/MPFR_RoundingMode.ml out/MPFR_Lib.ml out/MPFR_Add1sp1.ml out/Test_Add1sp1.ml -o out/Add1sp1
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

gen-tests: test/gen.c test/test_suite_mpfr_add1sp1
	cc -o test/gen test/gen.c -lmpfr -lgmp
	test/gen
	rm test/gen

clean:
	rm -rf out
	rm -f *~
	rm -f test/*~
