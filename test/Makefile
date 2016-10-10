all:
	+make clean
	$(MAKE) -C symmetric
	$(MAKE) -C ec
#	$(MAKE) -C hash
#	$(MAKE) -C hmac
#	$(MAKE) -C hkdf

FSTAR_HOME?=../../FStar
FSTAR=$(FSTAR_HOME)/bin/fstar.exe
FSTAR_ARGS=

HACL_HOME?=..
HACL_LIB=$(HACL_HOME)/lib/hst
HACL_KREMLIN=$(HACL_LIB)/kremlin
HACL_KREMLIN_FILES=$(addprefix $(HACL_KREMLIN)/, Hacl.UInt8.fst Hacl.UInt16.fst Hacl.UInt32.fst Hacl.UInt64.fst Hacl.UInt128.fst Hacl.Cast.fst Hacl.Policies.fst)
HACL_API=$(HACL_HOME)/crypto_hst
HACL_SYMMETRIC=$(HACL_API)/symmetric
HACL_EC=$(HACL_API)/ec

KREMLIN_HOME?=../../kremlin
KREMLIN=$(KREMLIN_HOME)/Kremlin.native
KREMLIN_ARGS=-verbose
KREMLIB=$(KREMLIN_HOME)/kremlib
KREMTEST=$(KREMLIN_HOME)/test

kremlin:
	$(MAKE) -C symmetric chacha-kremlin poly-kremlin aead-kremlin
	+make api-kremlin

api-kremlin:
	$(KREMLIN) $(KREMLIN_ARGS) \
		$(HACL_KREMLIN_FILES) $(HACL_API)/Hacl.Box.fst $(KREMTEST)/testlib.c c/test_api.c \
		-I $(HACL_LIB) -I $(HACL_API) -I $(HACL_SYMMETRIC) -I $(HACL_EC) \
		-I $(KREMLIB) -I $(KREMTEST)
	./a.out

clean:
	rm -rf *~ *.exe *.out *.o *.c *.h *.cmi *.cmo *.cmx *.krml
	$(MAKE) -C symmetric clean
	$(MAKE) -C ec clean
	$(MAKE) -C hash clean
	$(MAKE) -C hmac clean
	$(MAKE) -C hkdf clean
