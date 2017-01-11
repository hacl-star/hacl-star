#
# Main HACL* Makefile
#

.PHONY: prepare library

all: library

prepare:
	@echo $(CYAN)"\n# Installing OCaml packages required by F*"$(NORMAL)
	opam install ocamlfind batteries sqlite3 fileutils stdint zarith yojson pprint menhir
	@echo $(CYAN)"\n# Installing OCaml packages required by KreMLin"$(NORMAL)
	opam install ppx_deriving_yojson zarith pprint menhir ulex process fix wasm
	@echo $(CYAN)"\n# Compiling F*"$(NORMAL)
	make -C dependencies/FStar/src/ocaml-output
	@echo $(CYAN)"\n# Compiling KreMLin"$(NORMAL)
	make -C dependencies/kremlin
	@echo $(CYAN)"\nAll done ! Enjoy ;) "$(NORMAL)

library:
	@echo $(CYAN)"# Compiling the HaCl* library"$(NORMAL)
	mkdir -p build && cd build; \
	cmake -DCMAKE_C_COMPILER=$(GCC_EXEC) ../extracted/c && make
	@echo $(CYAN)"\nDone ! Generated libraries can be found in 'build'."$(NORMAL)

clean:
	@echo $(CYAN)"# Clean HaCl*"$(NORMAL)
	rm -rf *~
	rm -rf build


# Check if GCC-6 is installed, uses GCC otherwise
GCC_EXEC := $(shell gcc-6 --version 2>/dev/null | cut -c -5 | head -n 1)
ifdef INSTALL_EXEC
   INSTALL_EXEC := gcc-6
else
   INSTALL_EXEC := gcc
endif

NORMAL="\\033[0;39m"
CYAN="\\033[1;36m"
