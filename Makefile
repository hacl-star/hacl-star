#
# Main HACL* Makefile
#

.PHONY: lib-verify specs-verify specs-test code-verify code-extract code-test

all: display

display:
	@echo "HACL* Makefile:"
	@echo ""
	@echo "Standard Libraries (lib/)"
	@echo "- 'make lib-verify' will run the verification of the standard library"
	@echo ""
	@echo "Specifications (specs/)"
	@echo "- 'make specs-verify' will run the verification of the specifications"
	@echo "- 'make specs-test' will extract to OCaml and test the specifications"
	@echo ""
	@echo "Efficient code (code/)"
	@echo "- 'make code-verify' will run the verification of the efficient code"
	@echo "- 'make code-extract' will generate the efficient C code"
	@echo "- 'make code-test' will extract to C and test the specifications"
	@echo ""
	@echo "Build"
	@echo "- 'make build' will collect code and generate static/shared librairies"
	@echo "- 'make build-experimental' same, with experimental code"
	@echo "- 'make build/ml/libhacl.cmxa' will build an OCaml shared library from specs"


#
# Includes
#
ifneq ($(FSTAR_HOME),)
include Makefile.include
endif


#
# Targets
#

lib-verify:
	$(MAKE) -C lib

specs-verify:
	$(MAKE) -C specs

specs-test:
	$(MAKE) test -C specs

code-verify:
	@echo "Verifying Low* code"

code-extract:
	$(MAKE) -C code extract

code-snapshot: specs-verify
	$(MAKE) snapshot -C code

code-test: code-extract
	$(MAKE) test-snapshot -C code

build:
	mkdir -p build && cd build && cmake .. && make

build-experimental:
	@echo "Build Experimental"

build/ml/libhacl.cmxa:
	$(MAKE) -f Makefile.OCaml

#
# Packaging helper
#

.package-banner:
	@echo $(CYAN)"# Packaging the HACL* generated code"$(NORMAL)
	@echo $(CYAN)"  Make sure you have run verification before !"$(NORMAL)

package: .package-banner
	mkdir -p hacl
	cp -r dist/hacl-c/* hacl
	tar -zcvf hacl-star.tar.gz hacl
	rm -rf hacl
	@echo $(CYAN)"\nDone ! Generated archive is 'hacl-star.tar.gz'. !"$(NORMAL)

#
# CI
#

CC = $(GCC)

ci:
	$(MAKE) lib-verify
	$(MAKE) specs-verify
	$(MAKE) specs-test
# Temporary setting until code-verify, code-extract and code-test exist
	$(MAKE) -C code/hash
	$(MAKE) -C code/sha3
	#$(MAKE) -C code/blake2s
	$(MAKE) -C code/chacha20
	$(MAKE) -C code/salsa20
	$(MAKE) -C code/poly1305
	$(MAKE) -C code/chacha20poly1305
	$(MAKE) -C code/curve25519
	$(MAKE) -C code/nacl-box
	$(MAKE) -C code/experimental/aes-gcm || [[ "$(shell uname)" == "CYGWIN_NT"* ]]
	$(MAKE) -C code/frodo/spec
	$(MAKE) -C code/frodo/code TARGET=
	$(MAKE) -C code/ed25519
	$(MAKE) -C code/experimental/P256

#
# Clean
#

.clean-git:
	git reset HEAD --hard
	git clean -xffd

clean-base:
	rm -rf *~ *.tar.gz *.zip
	rm -rf dist/hacl-c/*.o
	rm -rf dist/hacl-c/libhacl*

clean-build:
	rm -rf build
	rm -rf build-experimental

clean-cache:
	rm -rf .cache

clean-hints:
	rm -rf .hints

clean: clean-base clean-build clean-cache

# Colors
NORMAL="\\033[0;39m"
CYAN="\\033[1;36m"
