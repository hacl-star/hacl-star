#
# Main HACL* Makefile
#

.PHONY: prepare build experimental clean

all: build

world: build experimental

prepare:
	@echo $(CYAN)"\n# Installing OCaml packages required by F*"$(NORMAL)
	opam install ocamlfind batteries sqlite3 fileutils stdint zarith yojson pprint menhir
	@echo $(CYAN)"\n# Installing OCaml packages required by KreMLin"$(NORMAL)
	opam install ppx_deriving_yojson zarith pprint menhir ulex process fix wasm
	@echo $(CYAN)"\n# Installing submodules for F* and KreMLin"$(NORMAL)
	git submodule update --init
	@echo $(CYAN)"\n# Compiling F*"$(NORMAL)
	$(MAKE) -C dependencies/FStar/src/ocaml-output
	$(MAKE) -C dependencies/FStar/ulib/ml
	@echo $(CYAN)"\n# Compiling KreMLin"$(NORMAL)
	$(MAKE) -C dependencies/kremlin
	@echo $(CYAN)"\nDone ! Run 'make' to compile the library."$(NORMAL)

build:
	@echo $(CYAN)"# Compiling the HaCl* library"$(NORMAL)
	mkdir -p build && cd build; \
	c$(MAKE) $(CMAKE_COMPILER_OPTION) .. && make
	@echo $(CYAN)"\nDone ! Generated libraries can be found in 'build'."$(NORMAL)

experimental:
	@echo $(CYAN)"# Compiling the HaCl* library (with experimental features)"$(NORMAL)
	mkdir -p build-experimental && cd build-experimental; \
	c$(MAKE) $(CMAKE_COMPILER_OPTION) -DExperimental=ON .. && make
	@echo $(CYAN)"\nDone ! Generated libraries can be found in 'build-experimental'."$(NORMAL)

ci:
	$(MAKE) -C test

hints:
	$(MAKE) -C code hints
	$(MAKE) -C secure_api hints
	$(MAKE) -C specs hints
	$(MAKE) -C test hints 

refresh-hints:
	$(MAKE) -B hints

%.verify-dir: %
	$(MAKE) -C $^ verify

verify: code.verify-dir secure_api.verify-dir specs.verify-dir test.verify-dir

clean:
	@echo $(CYAN)"# Clean HaCl*"$(NORMAL)
	rm -rf *~
	rm -rf build
	rm -rf build-experimental
	$(MAKE) -C specs clean
	$(MAKE) -C code clean
	$(MAKE) -C apps clean
	$(MAKE) -C test clean


# Check if GCC-6 is installed, uses GCC otherwise
GCC_EXEC := $(shell gcc-6 --version 2>/dev/null | cut -c -5 | head -n 1)
ifdef GCC_EXEC
   CMAKE_COMPILER_OPTION := -DCMAKE_C_COMPILER=gcc-6
endif

NORMAL="\\033[0;39m"
CYAN="\\033[1;36m"
