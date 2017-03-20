all: extract-c ct verify

DIRECTORIES= salsa-family bignum poly1305 curve25519 api

%-c: %
	$(MAKE) -C $< extract-c

%-ver: %
	$(MAKE) -C $< all-ver

%-ct: %
	$(MAKE) -C $< all-ct

%-ci: %
	$(MAKE) -C $< all-ci

%-hints: %
	$(MAKE) -C $< all-hints

verify: $(addsuffix -ver, $(DIRECTORIES))
ct: $(addsuffix -ct, $(DIRECTORIES))
extract-c: $(addsuffix -c, $(filter-out bignum, $(DIRECTORIES)))

ci: $(addsuffix -ci, $(DIRECTORIES))

hints: $(addsuffix -hints, $(DIRECTORIES))

bignum-hints:
	$(MAKE) -C bignum all-hints
	$(MAKE) -C poly1305 bignum-hints
	$(MAKE) -C curve25519 bignum-hints

clean:
	rm -rf *~ *.exe *.out 
	$(MAKE) -C salsa-family clean
	$(MAKE) -C bignum clean
	$(MAKE) -C poly1305 clean
	$(MAKE) -C curve25519 clean
	$(MAKE) -C api clean
