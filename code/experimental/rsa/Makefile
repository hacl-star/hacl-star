FSTAR_HOME?=../../../../FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
HACL_HOME?=../..
include ../../Makefile.include

RSA_FILES= \
	RSA.fst \
	BN.Convert.fst

%.fst-verify: %.fst
	$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../../lib  --lax $^

verify: $(addsuffix -verify, $(RSA_FILES))