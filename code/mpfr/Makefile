# For simplified Makefiles, define FSTAR_HOME, then include the file below.
FSTAR_HOME=~/.opam/4.05.0/packages.dev/fstar

all: add1sp1

include $(FSTAR_HOME)/ulib/ml/Makefile.include

# This target is very concise and re-uses the variables defined in
# Makefile.include. You shouldn't need to call `cp` ever.
add1sp1: out gen-tests MPFR.Lib.fst MPFR.Add1sp1.fst test/Test_Add1sp1.ml
	fstar.exe $(FSTAR_DEFAULT_ARGS) --lax --odir out --codegen OCaml MPFR.Lib.fst MPFR.Add1sp1.fst
	cp test/Test_Add1sp1.ml out/Test_Add1sp1.ml
	$(OCAMLOPT) -I $(FSTAR_HOME)/ulib/ml -I out out/MPFR_Lib.ml out/MPFR_Add1sp1.ml out/Test_Add1sp1.ml -o out/Add1sp1
	out/Add1sp1

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
