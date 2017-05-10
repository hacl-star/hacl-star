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

all-ci: ed25519-ci

clean: $(addsuffix -clean, $(DIRECTORIES))
	rm -rf *~ *.exe *.out *.graph
