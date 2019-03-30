HACL_HOME=../../../../..

include $(HACL_HOME)/Makefile.common

all:
	fstar.exe --extract Interop_Printer Interop_Printer.fst --codegen OCaml
	OCAMLPATH=$(FSTAR_HOME)/bin/ ocamlbuild -use-ocamlfind -package fstarlib Main.native

clean:
	rm Main.native Interop_Printer.ml
	rm -r _build/

