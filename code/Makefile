all: extract-c ct verify

DIRECTORIES=salsa-family bignum poly1305 curve25519 api hmac ed25519 hash
TOOSLOW=ed25519 hash

%-c: %
	$(MAKE) -C $< extract-c

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
ct: $(addsuffix -ct, $(DIRECTORIES))
extract-c: $(addsuffix -c, $(filter-out bignum, $(DIRECTORIES)))
hints: $(addsuffix -hints, $(DIRECTORIES))
ci: $(addsuffix -ci, $(filter-out $(TOOSLOW),$(DIRECTORIES)) experimental)

all-verify: verify
all-hints: hints
all-ci: ci
all-ct: ct

clean: $(addsuffix -clean, $(DIRECTORIES) experimental)
	rm -rf *~ *.exe *.out
