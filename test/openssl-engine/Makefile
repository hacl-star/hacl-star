OPENSSL_HOME?=../../../openssl
KREMLIN_HOME?=../../../kremlin
CURVE_HOME=../../code/curve25519/x25519-c
CHACHA_HOME=../../code/salsa-family/chacha-c
CFLAGS=-I$(OPENSSL_HOME)/include -L$(OPENSSL_HOME) -I$(KREMLIN_HOME)/kremlib \
  -I$(CURVE_HOME) -I$(CHACHA_HOME) -shared -Wno-unused-variable -Wno-parentheses -O3 -flto \
  -Wall
LDFLAGS=-lcrypto

ifeq ($(OS),Windows_NT)
  CC?=x86_64-w64-mingw32-gcc
  SO=dll
  PWD=$(shell cygpath -m $$(pwd))

all: OpenSSLEngine.$(SO) HaclEngine.$(SO) BCryptEngine.$(SO)
else
  SO=so
  CYGPATH=echo
  PWD=$(shell pwd)

all: OpenSSLEngine.$(SO) HaclEngine.$(SO)
endif

OpenSSLEngine.$(SO): HACLEngine.c
	$(CC) $(CFLAGS) -DIMPL=IMPL_OPENSSL $< -o $@ -shared $(LDFLAGS)

HaclEngine.$(SO): HACLEngine.c $(CURVE_HOME)/Curve25519.c $(CHACHA_HOME)/Chacha20.c
	$(CC) $(CFLAGS) -DIMPL=IMPL_HACL $^ -o $@ -shared $(LDFLAGS)

BCryptEngine.$(SO): BCryptEngine.c
	$(CC) $(CFLAGS) -DIMPL=IMPL_HACL $< -o $@ -shared $(LDFLAGS) -lbcrypt

.PHONY: test
test: test-OpenSSLEngine.$(SO) test-HaclEngine.$(SO)

test-%:
	@PATH=$(OPENSSL_HOME):"$(PATH)" \
	LD_LIBRARY_PATH=$(OPENSSL_HOME):"$(LD_LIBRARY_PATH)" \
	DYLD_LIBRARY_PATH=$(OPENSSL_HOME):"$(DYLD_LIBRARY_PATH)" \
	echo -e "engine $(PWD)/$*\nspeed ecdhx25519" | $(OPENSSL_HOME)/apps/openssl.exe
	echo -e "engine $(PWD)/$*\nspeed -evp chacha20" | $(OPENSSL_HOME)/apps/openssl.exe
	echo -e "engine $(PWD)/$*\nspeed -evp chacha20-poly1305" | $(OPENSSL_HOME)/apps/openssl.exe
