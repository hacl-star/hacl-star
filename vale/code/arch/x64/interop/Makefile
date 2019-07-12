all:
	fstar.exe --extract Interop_Printer Interop_Printer.fst --codegen OCaml
	ocamlbuild -use-ocamlfind Main.native

clean:
	rm Main.native Interop_Printer.ml
	rm -r _build/

