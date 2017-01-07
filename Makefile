#
# Main HACL* Makefile
#

.PHONY: prepare clean cleanall

prepare-fstar:
	opam install ocamlfind batteries sqlite3 fileutils stdint zarith yojson pprint menhir
	make -C dependencies/FStar/src/ocaml-output
	@echo "\n\nPlease set FSTAR_HOME before preparing kremlin\n\n"

prepare-kremlin:
	opam install ppx_deriving_yojson zarith pprint menhir ulex process fix wasm
	make -C dependencies/kremlin

