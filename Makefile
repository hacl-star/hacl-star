#
# Main HACL* Makefile
#

.PHONY: prepare build

all: build

prepare:
	@echo $(CYAN)"\n# Installing OCaml packages required by F*"$(NORMAL)
	opam install ocamlfind batteries sqlite3 fileutils stdint zarith yojson pprint menhir
	@echo $(CYAN)"\n# Installing OCaml packages required by KreMLin"$(NORMAL)
	opam install ppx_deriving_yojson zarith pprint menhir ulex process fix wasm
	@echo $(CYAN)"\n# Installing submodules for F* and KreMLin"$(NORMAL)
	git submodule update --init
	@echo $(CYAN)"\n# Compiling F*"$(NORMAL)
	make -C dependencies/FStar/src/ocaml-output
	@echo $(CYAN)"\n# Compiling KreMLin"$(NORMAL)
	make -C dependencies/kremlin
	@echo $(CYAN)"\nDone ! Run 'make' to compile the library."$(NORMAL)

build:
	@echo $(CYAN)"# Compiling the HaCl* library"$(NORMAL)
	mkdir -p build && cd build; \
	cmake $(CMAKE_COMPILER_OPTION) ../snapshots/hacl-c && make
	@echo $(CYAN)"\nDone ! Generated libraries can be found in 'build'."$(NORMAL)

clean:
	@echo $(CYAN)"# Clean HaCl*"$(NORMAL)
	rm -rf *~
	rm -rf build


# Check if GCC-6 is installed, uses GCC otherwise
GCC_EXEC := $(shell gcc-6 --version 2>/dev/null | cut -c -5 | head -n 1)
ifdef GCC_EXEC
   CMAKE_COMPILER_OPTION := -DCMAKE_C_COMPILER=gcc-6
endif

NORMAL="\\033[0;39m"
CYAN="\\033[1;36m"
