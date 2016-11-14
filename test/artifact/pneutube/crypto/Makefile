FSTAR_HOME?=../../../../../FStar
KREMLIN_HOME=$(FSTAR_HOME)/../kremlin
ARTIFACT_HOME=../..
include ../../Makefile.include

MODULES=Hacl.Symmetric.Poly1305_64.Parameters \
	Hacl.Symmetric.Poly1305_64.Bigint \
	Hacl.Symmetric.Poly1305_64 \
	Hacl.EC.Curve25519.Parameters \
	Hacl.EC.Curve25519.Bigint \
	Hacl.EC.Curve25519.Utils \
	Hacl.EC.Curve25519.Bignum.Fdifference \
	Hacl.EC.Curve25519.Bignum.Fproduct \
	Hacl.EC.Curve25519.Bignum.Fscalar \
	Hacl.EC.Curve25519.Bignum.Fsum \
	Hacl.EC.Curve25519.Bignum.Modulo \
	Hacl.EC.Curve25519.Bignum \
	Hacl.EC.Curve25519.Crecip \
	Hacl.EC.Curve25519.PPoint \
	Hacl.EC.Curve25519.AddAndDouble \
	Hacl.EC.Curve25519.Ladder \
	Hacl.EC.Curve25519 \
	Hacl.Symmetric.HSalsa20 \
	Hacl.Symmetric.XSalsa20 \
	Hacl.SecretBox \
	Hacl.Box

INCLUDES=

ver: $(addsuffix .fst-ver, $(MODULES))

test: Hacl.Test.fst
	$(KREMLIN) $(KREMLIN_ARGS) $^ -no-prefix Hacl.Test -add-include '"testlib.h"' \
		$(KREMTEST)/testlib.c -I $(LIB_KRML) -I $(KREMLIB) -I $(KREMTEST) \
		-tmpdir tmp -o test_crypto.exe
	./test_crypto.exe

extract: Hacl.Test.fst
	$(KREMLIN) $(KREMLIN_ARGS) $^ -no-prefix Hacl.Test -add-include '"testlib.h"' \
		$(KREMTEST)/testlib.c -I $(LIB_KRML) -I $(KREMLIB) -I $(KREMTEST) \
		-tmpdir extracted_code -skip-compilation
	./test_crypto.exe


clean:
	rm -rf tmp
	rm -f *~ *.exe
