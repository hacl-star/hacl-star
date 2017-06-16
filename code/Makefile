all: extract-c ct verify

DIRECTORIES=salsa-family bignum poly1305 curve25519 api ed25519 hash hmac

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

# Gathering all bignum verification code in one target to allow parallelization of the others
bignum-hints:
	$(MAKE) -C bignum all-hints
	$(MAKE) -C poly1305 bignum-hints
	$(MAKE) -C curve25519 bignum-hints

poly1305-specific-hints:
	$(MAKE) -C poly1305 specific-hints

x25519-specific-hints:
	$(MAKE) -C curve25519 specific-hints

hints: $(addsuffix -hints, salsa-family api) bignum-hints poly1305-specific-hints x25519-specific-hints

bignum-ci:
	$(MAKE) -C poly1305 bignum-ci
	$(MAKE) -C curve25519 bignum-ci

poly1305-specific-ci:
	$(MAKE) -C poly1305 specific-ci

x25519-specific-ci:
	$(MAKE) -C curve25519 specific-ci

experimental-ci:
	$(MAKE) -C experimental all-ci

hash-ci:
	$(MAKE) -C hash all-ci

hmac-ci:
	$(MAKE) -C hmac all-ci

ci: $(addsuffix -ci, hash salsa-family api ed25519 bignum poly1305-specific x25519-specific experimental)

clean:
	rm -rf *~ *.exe *.out
	$(MAKE) -C salsa-family clean
	$(MAKE) -C bignum clean
	$(MAKE) -C poly1305 clean
	$(MAKE) -C curve25519 clean
	$(MAKE) -C api clean
	$(MAKE) -C experimental clean
	$(MAKE) -C hash clean
	$(MAKE) -C hmac clean
