HACL_HOME=../..
include $(HACL_HOME)/Makefile.common

UNZIP = unzip -o
WGET  = wget
PROB  = 1

Spec.ECDSA.Test.Vectors.fst: Spec.ECDSA.Test.Vectors.fstp SigVer.rsp
	cat $< > $@
	python3 cavp_parse.py --prob $(PROB) $(word 2,$^) >> $@

SigVer.rsp: 186-4ecdsatestvectors.zip
	$(UNZIP) $^ 186-4ecdsatestvectors/$@
	mv 186-4ecdsatestvectors/$@ .
	rmdir 186-4ecdsatestvectors

186-4ecdsatestvectors.zip:
	$(WGET) https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/dss/$@

.PHONY: clean
clean:
	rm -f *.zip *.rsp Spec.ECDSA.Test.Vectors.fst *~
