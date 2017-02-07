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
	$(MAKE) -C ../crypto_proofs krml-test.exe

extract-c: extract-c-code extract-c-crypto

ct:
	$(MAKE) -C ../code ct

verify-code:
	$(MAKE) -C ../code ci

verify-crypto:
	$(MAKE) -C ../crypto_proofs all-ver

verify: verify-code verify-crypto


clean:
	$(MAKE) -C ../code clean
	$(MAKE) -C ../crypto_proofs clean
