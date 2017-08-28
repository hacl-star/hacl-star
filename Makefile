#
# Main HACL* Makefile
#

.PHONY: display verify test clean

all: display

display:
	@echo "HaCl* Makefile:"
	@echo "- 'verify' will run F* verification on all specs, code and secure-api directories"
	@echo "- 'extract' will generate all the C code into a snapshot and test it (no verification)"
	@echo "- 'build' will generate both static and shared libraries (no verification)"
	@echo "- 'test' will generate and test everything (no verification)"
	@echo "- 'world' will run everything (except make prepare)"
	@echo "- 'clean' will remove all artifacts of other targets"
	@echo ""
	@echo "Specialized targets for Experts:"
	@echo "- 'verify-ct' will run F* verification of the code for the side-channel resistance"
	@echo "- 'verify-specs' will run F* verification on the specifications"
	@echo "- 'verify-code' will run F* verification on the code against the specification"
	@echo "- 'verify-secure_api' will run F* verification of the secure_api directory"
	@echo "- 'extract-specs' will generate OCaml code for the specifications"
	@echo "- 'extract-c-code' will generate C code for all the stable primitives"
	@echo "- 'extract-c-code-experimental' will generate C code for experimental primitives"
	@echo "- 'extract-all' will generate all versions of the C snapshots available"
	@echo "- 'prepare' will install F* and Kremlin (Requirements are still needed)"
	@echo "- 'clean-snapshots' will remove all snapshots"

#
# Includes
#

include Makefile.include
include Makefile.build

#
# Verification
#

.verify-banner:
	@echo $(CYAN)"# Verification of the HaCl*"$(NORMAL)

verify-ct:
	$(MAKE) -C code ct

verify-specs: specs.dir-verify
verify-code: code.dir-verify
verify-secure_api: secure_api.dir-verify

verify: .verify-banner verify-ct verify-specs verify-code verify-secure_api
	@echo $(CYAN)"\nDone ! Please check the verification output"$(NORMAL)

#
# Code generation
#

.extract-banner:
	@echo $(CYAN)"# Generation of the HaCl* verified C code"$(NORMAL)
	@echo $(CYAN)" (This is not running formal verification)"$(NORMAL)

extract: .extract-banner snapshots/hacl-c
	@echo $(CYAN)"\nDone ! Generated code can be found in 'snapshots/hacl-c'."$(NORMAL)

extract-specs:
	$(MAKE) -C specs

extract-all: snapshots-all

#
# Compilation of the library
#

.build-banner:
	@echo $(CYAN)"# Compiling the HaCl* library"$(NORMAL)

build-make:
	$(MAKE) build/libhacl.so
	$(MAKE) build/libhacl32.so

build-cmake:
	mkdir -p build && cd build && CC=gcc cmake $(CMAKE_COMPILER_OPTION) .. && make

build:
	$(MAKE) build-make
	$(MAKE) build-cmake
	@echo $(CYAN)"\nDone ! Generated libraries can be found in 'build'."$(NORMAL)

#
# Test specification and code
#

test:
	@echo $(CYAN)"# Testing the HaCl* code and specifications"$(NORMAL)
	$(MAKE) -C test

#
# World
#

world: .clean-banner .clean-git .clean-snapshots
	$(MAKE) verify
	$(MAKE) extract-specs
	$(MAKE) extract-all
	$(MAKE) build
	$(MAKE) test
	$(MAKE) package

#
# CI
#

ci: .clean-banner .clean-git .clean-snapshots
	$(MAKE) test

#
# Clean
#

.clean-banner:
	@echo $(CYAN)"# Clean HaCl*"$(NORMAL)

.clean-git:
	git reset HEAD --hard
	git clean -xfd

.clean-snapshots: snapshots-remove

clean-base:
	rm -rf *~ *.tar.gz

clean-build:
	rm -rf build
	rm -rf build-experimental

clean-package: clean-base clean-build

clean: .clean-banner clean-base clean-build
	$(MAKE) -C specs clean
	$(MAKE) -C code clean
	$(MAKE) -C secure_api clean
	$(MAKE) -C apps clean
	$(MAKE) -C test clean

#
# Installation helper
#

prepare:
	@echo "# Installing OCaml packages required by F*"
	opam install ocamlfind batteries sqlite3 fileutils stdint zarith yojson pprint menhir
	@echo "# Installing OCaml packages required by KreMLin"
	opam install ppx_deriving_yojson zarith pprint menhir ulex process fix wasm
	@echo "# Installing submodules for F* and KreMLin"
	git submodule update --init
	@echo "# Compiling and Installing F*"
	$(MAKE) -C dependencies/FStar/src/ocaml-output
	$(MAKE) -C dependencies/FStar/ulib/ml
	@echo "# Compiling and Installing KreMLin"
	$(MAKE) -C dependencies/kremlin

#
# Packaging helper
#

.package-banner:
	@echo $(CYAN)"# Packaging the HaCl* generated code"$(NORMAL)
	@echo $(CYAN)"  Make sure you have run verification before !"$(NORMAL)

package: .package-banner snapshots/hacl-c build
	mkdir -p hacl
	cp build/lib* hacl
	cp -r snapshots/hacl-c/* hacl
	tar -zcvf hacl-star.tar.gz hacl
	rm -rf hacl
	@echo $(CYAN)"\nDone ! Generated archive is 'hacl-star.tar.gz'. !"$(NORMAL)

#
# Undocumented targets
#

experimental:
	@echo $(CYAN)"# Compiling the HaCl* library (with experimental features)"$(NORMAL)
	mkdir -p build-experimental && cd build-experimental; \
	cmake $(CMAKE_COMPILER_OPTION) -DExperimental=ON .. && make
	@echo $(CYAN)"\nDone ! Generated libraries can be found in 'build-experimental'."$(NORMAL)

hints: code.dir-hints secure_api.dir-hints specs.dir-hints

