include $(HACL_HOME)/Makefile.include

.PHONY=all test

FSTAR_INCLUDES+= \
	--include $(HACL_HOME)/lib \
	--include $(HACL_HOME)/lib/fst \
	--include $(HACL_HOME)/specs/lemmas

FSTAR_OPTS = \
	--expose_interfaces

LIBS = Lib.IntTypes.fst Lib.RawIntTypes.fst Lib.Sequence.fst Lib.ByteSequence.fst
LIBS_FILES= $(addprefix $(HACL_HOME)/lib/fst/, $(LIBS))
LIBS_ML = Lib_IntTypes.ml Lib_RawIntTypes.ml Lib_Sequence.ml Lib_ByteSequence.ml
LIBS_EX = --extract_module Lib.IntTypes --extract_module Lib.RawIntTypes  --extract_module Lib.Sequence --extract_module Lib.ByteSequence

test.exe: $(LIBS_FILES) Test.fst
	mkdir -p ml-test
	$(FSTAR) $(FSTAR_OPTS) --codegen OCaml --lax $(LIBS_EX) --extract_module Test --odir ml-test $^
	@echo 'let _ = test()' >> ml-test/Test.ml
	$(OCAMLOPT) -I ml-test $(addprefix ml-test/, $(LIBS_ML))  ml-test/Test.ml -o test.exe
	./test.exe

clean:
	rm -rf *~ *.exe ml-test
