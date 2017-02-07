all: extract-c ct verify

DIRECTORIES= salsa-family bignum poly1305 curve25519

%-c: %
	$(MAKE) -C $< extract-c

%-ver: %
	$(MAKE) -C $< all-ver

%-ct: %
	$(MAKE) -C $< all-ct

verify: $(addsuffix -ver, $(DIRECTORIES))
ct: $(addsuffix -ct, $(DIRECTORIES))
extract-c: $(addsuffix -c, $(filter-out bignum, $(DIRECTORIES)))

clean:
	rm -rf *~ *.exe *.out 
	$(MAKE) -C salsa-family clean
	$(MAKE) -C bignum clean
	$(MAKE) -C poly1305 clean
	$(MAKE) -C curve25519 clean
