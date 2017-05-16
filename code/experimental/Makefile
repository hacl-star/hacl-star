HACL_HOME?=../..
KREMLIN_HOME?=$(HACL_HOME)/kremlin
FSTAR_HOME?=$(HACL_HOME)/kremlin


DIRECTORIES=ed25519 hash salsa-family

%-c: %
	$(MAKE) -C $< extract-c

%-clean: %
	$(MAKE) -C $< clean

extract-c: $(addsuffix -c, $(DIRECTORIES))

ed25519-ci:
	$(MAKE) -C ed25519 all-ci

sha2-ci:
	$(MAKE) -C hash all-ci

salsa-family-ci:
	$(MAKE) -C salsa-family all-ci

all-ci: ed25519-ci sha2-ci salsa-family-ci

ed25519-ct:
	$(MAKE) -C ed25519 all-ct

all-ct: ed25519-ct

clean: $(addsuffix -clean, $(DIRECTORIES))
	rm -rf *~ *.exe *.out *.graph
