OPENSSL_HOME?=../../../openssl
KREMLIN_HOME?=../../../kremlin
CURVE_HOME=../../code/curve25519/x25519-c
CHACHA_HOME=../../code/salsa-family/chacha-c
POLY_HOME=../../code/poly1305/poly-c
CFLAGS=-I$(OPENSSL_HOME)/include -L$(OPENSSL_HOME) -I$(KREMLIN_HOME)/kremlib \
  -I$(CURVE_HOME) -I$(CHACHA_HOME) -I$(CHACHA_HOME)/.. -I$(POLY_HOME) -I$(OPENSSL_HOME) \
  -shared -Wall -Wno-unused-variable -Wno-parentheses -O3 -flto
LDFLAGS=-lcrypto

# Some notes. OpenSSL does not expose its implementation of Poly1305 standalone,
# and we do want to access it to benchmark Poly1305 without the overhead of
# AEAD. On OSX and Linux, all the symbols from libcrypto.dll are visible,
# meaning we can happily include the internal header for OpenSSL's then link
# without trouble. On Windows, the visibility of symbols is controlled by a
# specific file. Rather than patch OpenSSL, we include a couple object files,
# along with a stub in HACLEngine.c. This is probably a blatant violation of
# ODR.

ifeq ($(OS),Windows_NT)
CC=x86_64-w64-mingw32-gcc
SO=dll
PWD=$(shell cygpath -m $$(pwd))
BCRYPTDLL=BCryptEngine.dll
BONUS_OBJ=$(addprefix $(OPENSSL_HOME)/crypto/poly1305/,poly1305.o poly1305-x86_64.o) \
  $(OPENSSL_HOME)/crypto/x86_64cpuid.o
else
SO=so
PWD=$(shell pwd)
BCRYPTDLL=
BONUS_OBJ=
endif

all: OpenSSLEngine.$(SO) HaclEngine.$(SO) $(BCRYPTDLL)

OpenSSLEngine.$(SO): HACLEngine.c
	$(CC) $(CFLAGS) -DIMPL=IMPL_OPENSSL $< $(BONUS_OBJ) -o $@ -shared $(LDFLAGS)

HaclEngine.$(SO): HACLEngine.c $(CURVE_HOME)/Curve25519.c $(CHACHA_HOME)/Chacha20.c $(POLY_HOME)/Poly1305_64.c
	$(CC) $(CFLAGS) -DIMPL=IMPL_HACL $^ -o $@ -shared $(LDFLAGS)

BCryptEngine.$(SO): BCryptEngine.c
	$(CC) $(CFLAGS) -DIMPL=IMPL_HACL $< -o $@ -shared $(LDFLAGS) -lbcrypt

.PHONY: test
test: test-OpenSSLEngine.$(SO) test-HaclEngine.$(SO)

test-%: all
	./test.sh "$(OPENSSL_HOME)" "$(PWD)/$*"
