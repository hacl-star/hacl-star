all: extract-c ct verify

# The bignum directory is not included because it is independently
# checked by curve25519 and poly1305 with specific parameters
DIRECTORIES=uint128 salsa-family poly1305 poly1305_32 curve25519 api hmac ed25519 hash lib lib/kremlin
TOOSLOW=experimental

%-c: %
	$(MAKE) -C $< extract-c

%-test: %
	$(MAKE) -C $< test

%-ver: %
	$(MAKE) -C $< all-ver

%-ct: %
	$(MAKE) -C $< all-ct

%-ci: %
	$(MAKE) -C $< all-ci

%-hints: %
	$(MAKE) -C $< hints

%-clean: %
	$(MAKE) -C $< clean

verify: $(addsuffix -ver, $(filter-out $(TOOSLOW),$(DIRECTORIES)))
test: $(addsuffix -test, $(DIRECTORIES))
ct: $(addsuffix -ct, $(DIRECTORIES))
extract-c: $(addsuffix -c, $(filter-out bignum, $(DIRECTORIES)))
hints: $(addsuffix -hints, $(DIRECTORIES))
ci: $(addsuffix -ci, $(filter-out $(TOOSLOW),$(DIRECTORIES)))

all-verify: verify
all-hints: hints
all-ci: ci
all-ct: ct
all-test: test

clean: $(addsuffix -clean, $(DIRECTORIES) experimental)
	rm -rf *~ *.exe *.out
