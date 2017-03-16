OPENSSL_HOME?=../../../openssl
KREMLIN_HOME?=../../../kremlin
CURVE_HOME=../../code/curve25519/x25519-c
CHACHA_HOME=../../code/salsa-family/chacha-c
POLY_HOME=../../code/poly1305/poly-c
CFLAGS=-I$(OPENSSL_HOME)/include -L$(OPENSSL_HOME) -I$(KREMLIN_HOME)/kremlib \
  -I$(CURVE_HOME) -I$(CHACHA_HOME) -I$(CHACHA_HOME)/.. -I$(POLY_HOME) -I$(OPENSSL_HOME) \
  -shared -Wall -Wno-unused-variable -Wno-parentheses -O3 -flto
LDFLAGS=-lcrypto

ifeq ($(OS),Windows_NT)
CC?=x86_64-w64-mingw32-gcc
SO=dll
EXE=.exe
PWD=$(shell cygpath -m $$(pwd))

all: OpenSSLEngine.$(SO) HaclEngine.$(SO) BCryptEngine.$(SO)
else
SO=so
EXE=
CYGPATH=echo
PWD=$(shell pwd)

all: OpenSSLEngine.$(SO) HaclEngine.$(SO)
endif

OpenSSLEngine.$(SO): HACLEngine.c
	$(CC) $(CFLAGS) -DIMPL=IMPL_OPENSSL $< -o $@ -shared $(LDFLAGS)

HaclEngine.$(SO): HACLEngine.c $(CURVE_HOME)/Curve25519.c $(CHACHA_HOME)/Chacha20.c $(POLY_HOME)/Poly1305_64.c
	$(CC) $(CFLAGS) -DIMPL=IMPL_HACL $^ -o $@ -shared $(LDFLAGS)

BCryptEngine.$(SO): BCryptEngine.c
	$(CC) $(CFLAGS) -DIMPL=IMPL_HACL $< -o $@ -shared $(LDFLAGS) -lbcrypt

.PHONY: test
test: test-OpenSSLEngine.$(SO) test-HaclEngine.$(SO)

OPENSSL_EXE=$(OPENSSL_HOME)/apps/openssl$(EXE)

test-%: all
	./test.sh "$(OPENSSL_HOME)" "$(PWD)/$*"

