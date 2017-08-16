#
# Main HACL* Makefile
#

.PHONY: verify verify_all test nss dependencies clean

all: nss

verify:
	@echo $(CYAN)"# Verifying the HaCl* code (specialized for NSS)"$(NORMAL)
	$(MAKE) -C specs Spec.Curve25519.fst-verify
	$(MAKE) verify -C code/curve25519

verify_all:
	@echo $(CYAN)"# Verifying all the HaCl* code"$(NORMAL)
	$(MAKE) verify -C specs
	$(MAKE) verify -C code

build: dependencies
	@echo $(CYAN)"# Generating the HaCl* code (specialized for NSS)"$(NORMAL)
	$(MAKE) nss-snapshot -C test
	@touch build
	@echo $(CYAN)"\nDone ! Generated code can be found in 'snapshots/nss'."$(NORMAL)

test: build
	$(MAKE) -C snapshots/nss unit-tests unit-tests-32

nss: test
	@echo $(CYAN)"# Generating production code from the NSS snapshot"$(NORMAL)
	$(MAKE) nss-production -C test
	@echo $(CYAN)"\nDone ! Generated code can be found in 'snapshots/nss-production'."$(NORMAL)

dependencies:
	@echo $(CYAN)"# Get and build F* and KreMLin"$(NORMAL)
	opam switch 4.04.2
	eval `opam config env`
	git submodule update --init
	opam config exec -- make -C dependencies/FStar/src/ocaml-output
	opam config exec -- make -C dependencies/kremlin

clean:
	@echo $(CYAN)"# Clean HaCl*"$(NORMAL)
	rm -rf *~ build snapshots
	$(MAKE) -C specs clean
	$(MAKE) -C code clean
	$(MAKE) -C dependencies/FStar/src/ocaml-output clean
	$(MAKE) -C dependencies/kremlin clean

NORMAL="\\033[0;39m"
CYAN="\\033[1;36m"
