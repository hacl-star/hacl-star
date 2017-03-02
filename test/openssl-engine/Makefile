ifeq ($(OS),Windows_NT)
  CC?=x86_64-w64-mingw32-gcc
  SO=dll
else
  SO=so
endif
OPENSSL_HOME?=../../../openssl
KREMLIN_HOME?=../../../kremlin
CURVE_HOME=../../code/curve25519/x25519-c
CFLAGS=-I$(OPENSSL_HOME)/include -L$(OPENSSL_HOME) -I$(KREMLIN_HOME)/kremlib \
  -I$(CURVE_HOME) -shared -Wno-unused-variable -Wno-parentheses -O3 -flto \
  -Wall
LDFLAGS=-lcrypto

OpenSSLEngine.$(SO): HACLEngine.c
	$(CC) $(CFLAGS) -DIMPL=IMPL_OPENSSL $< -o $@ -shared $(LDFLAGS)

HaclEngine.$(SO): HACLEngine.c $(CURVE_HOME)/Curve25519.c
	$(CC) $(CFLAGS) -DIMPL=IMPL_HACL $^ -o $@ -shared $(LDFLAGS)

BCryptEngine.$(SO): BCryptEngine.c
	$(CC) $(CFLAGS) -DIMPL=IMPL_HACL $< -o $@ -shared $(LDFLAGS) -lbcrypt
