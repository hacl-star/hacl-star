HACL_HOME:../../..

include ../../Makefile.include

all: extract-c

extract-c: Hacl_AES.c

aesgcm-c/out.krml: $(wildcard Crypto.Symmetric.AES*.fst)
	$(KREMLIN) $(KREMLIN_ARGS) \
	  -tmpdir aesgcm-c \
	  $^ -skip-translation

Hacl_AES.c: aesgcm-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) \
	  -bundle 'Crypto.Symmetric.AES+Crypto.Symmetric.AES128=*[rename=Hacl_AES]' \
	  -tmpdir aesgcm-c \
	  -minimal -add-include '"kremlib.h"' \
	  -skip-compilation $<
