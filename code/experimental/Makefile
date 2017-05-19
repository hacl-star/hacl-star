HACL_HOME?=../..
KREMLIN_HOME?=$(HACL_HOME)/kremlin
FSTAR_HOME?=$(HACL_HOME)/kremlin


DIRECTORIES=

%-c: %
	$(MAKE) -C $< extract-c

%-clean: %
	$(MAKE) -C $< clean

extract-c: $(addsuffix -c, $(DIRECTORIES))

all-ci:

all-ct:

clean: $(addsuffix -clean, $(DIRECTORIES))
	rm -rf *~ *.exe *.out *.graph
