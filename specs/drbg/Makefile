HACL_HOME=../..
include $(HACL_HOME)/Makefile.common

UNZIP = unzip -o
WGET  = wget
PROB  = 30

Spec.HMAC_DRBG.Test.Vectors.fst: Spec.HMAC_DRBG.Test.Vectors.fstp HMAC_DRBG.rsp
	cat $< > $@
	python3 cavp_parse.py --prob $(PROB) $(word 2,$^) >> $@

HMAC_DRBG.rsp: drbgvectors_pr_false.zip
	$(UNZIP) $^ $@

drbgvectors_pr_false.zip: drbgtestvectors.zip
	$(UNZIP) $^ $@

drbgtestvectors.zip:
	$(WGET) https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/drbg/$@

.PHONY: clean
clean:
	rm -f *.zip *.rsp Spec.HMAC_DRBG.Test.Vectors.fst *~
