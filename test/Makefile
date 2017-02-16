HACL_HOME?=../..
KREMLIN_HOME?=$(HACL_HOME)/kremlin
FSTAR_HOME?=$(HACL_HOME)/kremlin

.PHONY: snapshot

all:
	$(MAKE) extract-c
	$(MAKE) ct
	$(MAKE) verify

travis:
	$(MAKE) extract-c
	$(MAKE) ct
	$(MAKE) -C .. world

extract-c-code:
	$(MAKE) -C ../code extract-c

extract-c-crypto:
	$(MAKE) -C ../secure_api krml-test.exe

extract-c: extract-c-code extract-c-crypto

ct:
	$(MAKE) -C ../code ct

verify-code:
	$(MAKE) -C ../code ci

verify-crypto:
	$(MAKE) -C ../secure_api all-hints

hints-code:
	$(MAKE) -C ../code hints

hints-crypto:
	$(MAKE) -C ../secure_api all-hints

hints: hints-code hints-crypto

verify: verify-code verify-crypto

snapshot: extract-c-code
	mkdir -p snapshot
	cp ../code/poly1305/poly-c/Poly1305_64.* ../code/curve25519/x25519-c/Curve25519.* \
		../code/salsa-family/chacha-c/Chacha20.* ../code/salsa-family/salsa-c/Salsa20.* \
		snapshot
	cp $(addprefix ../snapshots/hacl-c/, test-chacha.c test-curve.c testlib.c testlib.h test-poly.c test-salsa.c Makefile) snapshot
	cp $(addprefix $(KREMLIN_HOME)/kremlib/, native128.* kremlib.* gcc_compat.h) snapshot

test-snapshot: snapshot
	$(MAKE) -C snapshot test-chacha test-curve test-poly test-salsa

clean:
	$(MAKE) -C ../code clean
	$(MAKE) -C ../secure_api clean
	rm -rf snapshot *.o *.exe *~
