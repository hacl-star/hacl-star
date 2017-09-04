#
# Main HACL* Makefile
#

.PHONY: display verify test clean

all: display

display:
	@echo "HACL* Makefile:"
	@echo "If you want to run and test the C library:"
	@echo "- 'make build' will generate a shared library from the hacl-c snapshot (no verification)"
	@echo "- 'make unit-tests' will run tests on the library built rom the hacl-c snapshot (no verification)"
	@echo "- 'make clean-build' will clean 'build' artifacts"
	@echo ""
	@echo "If you want to verify the F* code and regenerate the C library:"
	@echo "- 'make prepare' will try to install F* and Kremlin (still has some prerequisites)"
	@echo "- 'make verify' will run F* verification on all specs, code and secure-api directories"
	@echo "- 'make extract' will generate all the C code into a snapshot and test it (no verification)"
	@echo "- 'make test-all' will generate and test everything (no verification)"
	@echo "- 'make world' will run everything (except make prepare)"
	@echo "- 'make clean' will remove all artifacts created by other targets"
	@echo ""
	@echo "Specialized targets for Experts:"
	@echo "- 'make verify-ct' will run F* verification of the code for the secret independance"
	@echo "- 'make verify-specs' will run F* verification on the specifications"
	@echo "- 'make verify-code' will run F* verification on the code against the specification"
	@echo "- 'make verify-secure_api' will run F* verification of the secure_api directory"
	@echo "- 'make extract-specs' will generate OCaml code for the specifications"
	@echo "- 'make extract-all' will give you all versions of the C snapshots available"
	@echo "- 'make extract-new' will remove and regenerate all versions of the C snapshots available"
	@echo "- 'make extract-experimental' will generate C code for experimental primitives"


#
# Includes
#
ifneq ($(FSTAR_HOME),)
include Makefile.include
endif

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

extract: .extract-banner
	rm -rf snapshots/hacl-c snapshots/snapshot-gcc snapshots/snapshot-gcc-unrolled
	$(MAKE) snapshots/hacl-c
	@echo $(CYAN)"\nDone ! Generated code can be found in 'snapshots/hacl-c'."$(NORMAL)

extract-specs:
	$(MAKE) -C specs

extract-all: snapshots-all

extract-new: snapshots-update

extract-experimental: extract-c-code-experimental

#
# Compilation of the library
#

.build-banner:
	@echo $(CYAN)"# Compiling the HaCl* library"$(NORMAL)

build-make:
	$(MAKE) build/libhacl.so
#	$(MAKE) build/libhacl32.so

build-cmake:
	mkdir -p build && cd build && CC=gcc cmake $(CMAKE_COMPILER_OPTION) .. && make

build: clean-build
	$(MAKE) build-make
	@echo $(CYAN)"\nDone ! Generated libraries can be found in 'build'."$(NORMAL)

#
# Test specification and code
#

unit-tests:
	@echo $(CYAN)"# Testing the HaCl* shared library"$(NORMAL)
	$(MAKE) -C snapshots/hacl-c unit-tests
	$(MAKE) -C snapshots/hacl-c unit-tests32

test-all:
	@echo $(CYAN)"# Testing the HaCl* code and specifications"$(NORMAL)
	$(MAKE) -C test

#
# World
#

.base: verify extract-specs extract-all

world: .clean-banner .clean-git .clean-snapshots
	$(MAKE) verify
	$(MAKE) extract-specs
	$(MAKE) extract-all
	$(MAKE) build-make
	$(MAKE) test-all
	$(MAKE) package

#
# CI
#

ci: .clean-banner .clean-git .clean-snapshots
	$(MAKE) .base
	$(MAKE) build-make
	$(MAKE) test-all
	$(MAKE) package

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
	rm -rf snapshots/hacl-c/*.o
	rm -rf snapshots/hacl-c/libhacl*

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


# Colors
NORMAL="\\033[0;39m"
CYAN="\\033[1;36m"
