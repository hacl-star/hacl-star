#
# Main HACL* Makefile
#

.PHONY: setup

setup:
	@echo "\n# Installing OCaml packages required by F*"
	opam install ocamlfind batteries sqlite3 fileutils stdint zarith yojson pprint menhir
	@echo "\n# Installing OCaml packages required by KreMLin"
	opam install ppx_deriving_yojson zarith pprint menhir ulex process fix wasm
	@echo "\n# Compiling F*"
	make -C dependencies/FStar/src/ocaml-output
	@echo "\n# Compiling KreMLin"
	make -C dependencies/kremlin
	@echo "\nAll done ! Enjoy ;) "

