#
# Main HACL* Makefile
#

.PHONY: display verify test providers clean dependencies

all: display

display:
	@echo "HACL* Makefile:"
	@echo "If you want to run and test the C library:"
	@echo "- 'make build' will use CMake to generate static and shared libraries for snapshots/hacl-c (no verification)"
	@echo "- 'make build-make' will use Makefiles to do the same thing (no verification)"
	@echo "- 'make unit-tests' will run tests on the library built from the hacl-c snapshot (no verification)"
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
	@echo "- 'make extract-production' will remove and regenerate all C production snapshots available"
	@echo "- 'make extract-experimental' will generate C code for experimental primitives"
	@echo "- 'make build-experimental' will use CMake to generate experimental libraries with experimental features (no verification)"


#
# Includes
#
ifneq ($(FSTAR_HOME),)
include Makefile.include
endif

include Makefile.build
include Makefile.prepare


#
# Verification
#

.verify-banner:
	@echo $(CYAN)"# Verification of the HACL*"$(NORMAL)

verify-ct:
	$(MAKE) -C code ct

verify-specs: specs.dir-verify
verify-code: code.dir-verify
verify-secure_api: secure_api.dir-verify


verify: .verify-banner verify-ct verify-specs verify-code verify-secure_api
	@echo $(CYAN)"\nDone ! Please check the verification output"$(NORMAL)

verify-nss:
	@echo $(CYAN)"# Verification of the HACL* algorithms used by NSS"$(NORMAL)
	# Verify spec, code and ct
	$(MAKE) ct -C code/curve25519
	$(MAKE) verify -C code/curve25519
	$(MAKE) Spec.Curve25519.fst-verify -C specs
	$(MAKE) ct -C code/salsa-family
	$(MAKE) verify -C code/salsa-family
	$(MAKE) Spec.Chacha20.fst-verify -C specs
	$(MAKE) ct -C code/poly1305
	$(MAKE) verify -C code/poly1305
	$(MAKE) Spec.Poly1305.fst-verify -C specs
	$(MAKE) ct -C code/poly1305_32
	$(MAKE) verify -C code/poly1305_32


#
# Code generation
#

.extract-banner:
	@echo $(CYAN)"# Generation of the HACL* verified C code"$(NORMAL)
	@echo $(CYAN)" (This is not running formal verification)"$(NORMAL)

extract: .extract-banner
	$(MAKE) extract-production
	@echo $(CYAN)"\nDone ! Generated code for HACL* can be found in 'snapshots/hacl-c'."$(NORMAL)
	@echo $(CYAN)"Done ! Generated code for NSS can be found in 'snapshots/nss'."$(NORMAL)

extract-specs:
	$(MAKE) -C specs

extract-all:
	$(MAKE) snapshots-intermediates
	$(MAKE) snapshots-production

extract-production:
	$(MAKE) snapshots-remove-production
	$(MAKE) snapshots-production

extract-experimental: extract-c-code-experimental

#
# Compilation of the library
#

.build-banner:
	@echo $(CYAN)"# Compiling the HACL* library"$(NORMAL)

build-make:
	$(MAKE) build/libhacl.so
	$(MAKE) build/libhacl.a

build-cmake:
	mkdir -p build && cd build && cmake $(CMAKE_COMPILER_OPTION) .. && make

build: clean-build
	$(MAKE) build-cmake
	@echo $(CYAN)"\nDone ! Generated libraries can be found in 'build'."$(NORMAL)

#
# Test specification and code
#

unit-tests:
	@echo $(CYAN)"# Testing the HACL* shared library"$(NORMAL)
	$(MAKE) -C snapshots/hacl-c unit-tests

test-all:
	@echo $(CYAN)"# Testing the HACL* code and specifications"$(NORMAL)
	$(MAKE) -C test

#
# Providers
#

providers:
	@echo $(CYAN)"# Verifying, Extracting and Testing the Providers"$(NORMAL)
	$(MAKE) extract-c-code
	$(MAKE) -C providers

#
# CI
#

CC = $(GCC)

ci: .clean-banner .clean-git .clean-snapshots
	$(MAKE) -C lib
	$(MAKE) -C code/blake2 verify
	$(MAKE) -C code/sha3
	$(MAKE) -C frodo/spec
	$(MAKE) -C frodo/code TARGET=
	# $(MAKE) extract-specs
	# $(MAKE) extract-all
	# $(MAKE) -C code clean-c
	# $(MAKE) -C code extract-c
	# $(MAKE) -C providers/
	# $(MAKE) -C providers/test
	# $(MAKE) -C secure_api runtime_switch verify # test both extraction & verification
	# $(MAKE) test-all
	# $(MAKE) build-make
	# $(MAKE) package

#
# Clean
#

.clean-banner:
	@echo $(CYAN)"# Clean HACL*"$(NORMAL)

.clean-git:
	git reset HEAD --hard
	git clean -xfd

.clean-snapshots: snapshots-remove

clean-base:
	rm -rf *~ *.tar.gz *.zip
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
# Packaging helper
#

.package-banner:
	@echo $(CYAN)"# Packaging the HACL* generated code"$(NORMAL)
	@echo $(CYAN)"  Make sure you have run verification before !"$(NORMAL)

package: .package-banner
	mkdir -p hacl
	cp -r snapshots/hacl-c/* hacl
	tar -zcvf hacl-star.tar.gz hacl
	rm -rf hacl
	@echo $(CYAN)"\nDone ! Generated archive is 'hacl-star.tar.gz'. !"$(NORMAL)

#
# Undocumented targets
#

build-experimental:
	@echo $(CYAN)"# Compiling the HACL* library (with experimental features)"$(NORMAL)
	mkdir -p build-experimental && cd build-experimental; \
	cmake $(CMAKE_COMPILER_OPTION) -DExperimental=ON .. && make
	@echo $(CYAN)"\nDone ! Generated libraries can be found in 'build-experimental'."$(NORMAL)

hints: code.dir-hints secure_api.dir-hints specs.dir-hints


# Colors
NORMAL="\\033[0;39m"
CYAN="\\033[1;36m"
