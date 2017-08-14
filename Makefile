#
# Main HACL* Makefile
#

.PHONY: verify verify_all test nss-ci clean

all: build nss-ci

verify:
	@echo $(CYAN)"# Verifying the HaCl* code (specialized for NSS)"$(NORMAL)
	$(MAKE) verify -C specs/curve25519
	$(MAKE) verify -C code/curve25519

verify_all:
	@echo $(CYAN)"# Verifying all the HaCl* code"$(NORMAL)
	$(MAKE) verify -C specs
	$(MAKE) verify -C code

build:
	@echo $(CYAN)"# Generating the HaCl* code (specialized for NSS)"$(NORMAL)
	$(MAKE) nss-snapshot -C test
	@touch build
	@echo $(CYAN)"\nDone ! Generated code can be found in 'snapshots/nss'."$(NORMAL)

test: build
	$(MAKE) -C snapshots/nss unit-tests unit-tests-32

nss-ci: test
	@echo $(CYAN)"# Comparing the HaCl* code to production code"$(NORMAL)

clean:
	@echo $(CYAN)"# Clean HaCl*"$(NORMAL)
	rm -rf *~ build snapshots
	$(MAKE) -C specs clean
	$(MAKE) -C code clean

NORMAL="\\033[0;39m"
CYAN="\\033[1;36m"
