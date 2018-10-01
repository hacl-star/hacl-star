include ../../Makefile.include

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
