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
	$(MAKE) -C ../secure_api krml-test-vale.exe
	$(MAKE) -C ../secure_api krml-test-hacl.exe

extract-c: extract-c-code extract-c-crypto

ct:
	$(MAKE) -C ../code ct

verify-code:
	$(MAKE) -C ../code ci

verify-crypto:
	# Note: the all-hints target fails silently.
	$(MAKE) -C ../secure_api all-ver OTHERFLAGS=--record_hints

hints-code:
	$(MAKE) -C ../code hints

hints-crypto:
	$(MAKE) -C ../secure_api all-hints

hints: hints-code hints-crypto

verify: verify-code verify-crypto


clean:
	$(MAKE) -C ../code clean
	$(MAKE) -C ../secure_api clean
