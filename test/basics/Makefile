include $(HACL_HOME)/Makefile.include

.PHONY=all test


KREMLIN_INCLUDES+= \
	-I $(HACL_HOME)/lib \
	-I $(HACL_HOME)/lib/fst \
	-I $(KREMLIN_HOME)/include

KREMLIN_ARGS+=-verbose \
	-drop FStar,Prims,LowStar,C,C.*,Spec.*,Lib.*,WasmSupport \
	-ccopt -march=native

KREMLIN_TESTLIB=

LIBS = Lib.IntTypes.fst Lib.RawIntTypes.fst Lib.Sequence.fst Lib.ByteSequence.fst Lib.Buffer.fst Lib.ByteBuffer.fst
LIBS_FILES= $(addprefix $(HACL_HOME)/lib/fst/, $(LIBS))
LIBS_ML = Lib_IntTypes.ml Lib_RawIntTypes.ml Lib_Sequence.ml Lib_ByteSequence.ml
LIBS_EX = --extract_module Lib.IntTypes --extract_module Lib.RawIntTypes  --extract_module Lib.Sequence --extract_module Lib.ByteSequence



test-sequence.exe: $(LIBS_FILES) Test.Sequence.fst
	mkdir -p ml-test
	$(FSTAR) --expose_interfaces --codegen OCaml --lax $(LIBS_EX) --extract_module Test.Sequence --odir ml-test $^
	@echo 'let _ = test()' >> ml-test/Test_Sequence.ml
	$(OCAMLOPT) -I ml-test $(addprefix ml-test/, $(LIBS_ML))  ml-test/Test_Sequence.ml -o test-sequence.exe



%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@


c-test/out.krml: $(LIBS_FILES) Test.Buffer.fst
	$(KREMLIN) $(KREMLIN_ARGS) $(KREMLIN_INCLUDES) -fsopt "--expose_interfaces" -tmpdir c-test \
	-skip-translation $^


c-test/Test_Buffer.c: c-test/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) $(KREMLIN_TESTLIB) -tmpdir c-test -no-prefix Test.Buffer -skip-compilation $^ -o $@


test-buffer.exe: c-test/Test_Buffer.c ../../lib/c/Lib_Print.o
	$(CC) $(CFLAGS) -I $(KREMLIN_HOME) -I $(KREMLIN_HOME)/include -I $(KREMLIN_HOME)/kremlib/c -L $(KREMLIN_HOME)/kremlib/out -lkremlib -o $@ $^




build: test-sequence.exe test-buffer.exe

test:
	./test-sequence.exe
	./test-buffer.exe

all: test

clean:
	rm -rf *~ *.lax *.exe ml-test c-test
