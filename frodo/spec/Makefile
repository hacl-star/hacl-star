HACL_HOME=../..
FSTAR_HOME = $(HACL_HOME)/../FStar

include $(HACL_HOME)/Makefile.include

.PHONY = all test clean

FSTAR_INCLUDES += $(addprefix --include , $(HACL_HOME)/lib $(HACL_HOME)/lib/fst $(HACL_HOME)/specs)

OTHERFLAGS= --cache_checked_modules --cache_dir cache --use_hint_hashes --record_hints

SPECS = Spec.Frodo.Params Spec.Frodo.Lemmas Spec.Frodo Spec.Matrix

SPEC_FILES = $(addsuffix .fst, $(SPECS))

LIBS = Lib.IntTypes Lib.RawIntTypes Lib.Sequence Lib.ByteSequence

LIBS_FILES = $(addprefix $(HACL_HOME)/lib/fst/,$(addsuffix .fst, $(LIBS)))

LIBS_ML = $(addsuffix .ml, $(subst .,_, $(LIBS)))

LIBS_EX = --extract '$(LIBS)'

%.fst-verify: %.fst
	$(FSTAR) --hint_file hints/$(notdir $(subst .fst,,$<)).hints $<

hints: $(addsuffix .hints, $(SPEC_FILES))

verify: $(addsuffix -verify, $(SPEC_FILES))

all-hints: hints

all-ver: verify

all: test

test: frodo.exe
	./frodo.exe

frodo.exe: $(LIBS_FILES) $(HACL_HOME)/specs/Spec.Keccak.fst Spec.Matrix.fst Spec.Frodo.fst test/Spec.Frodo.Test.fst
	mkdir -p frodo-ml
	$(FSTAR) --codegen OCaml --lax $(LIBS_EX) \
	  --extract 'Spec.Keccak Spec.Frodo.Keccak Spec.Matrix Spec.Frodo.Params Spec.Frodo.Encode Spec.Frodo.Pack Spec.Frodo Spec.Frodo.Test' \
	  --odir frodo-ml --expose_interfaces \
	  $^
	@echo 'let _ = test()' >> frodo-ml/Spec_Frodo_Test.ml
	$(OCAMLOPT) -I frodo-ml $(addprefix frodo-ml/, $(LIBS_ML)) \
	  frodo-ml/Spec_Keccak.ml frodo-ml/Spec_Matrix.ml frodo-ml/Spec_Frodo_Params.ml frodo-ml/Spec_Frodo_Keccak.ml frodo-ml/Spec_Frodo_Encode.ml \
	  frodo-ml/Spec_Frodo_Pack.ml frodo-ml/Spec_Frodo.ml frodo-ml/Spec_Frodo_Test.ml \
          -o frodo.exe

clean:
	rm -rf *.cmi *.cmo *.cmx *.o *~ *.out *.exe *-ml
