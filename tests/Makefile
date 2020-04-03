# A minimalistic Makefile for all testing options.

KREMLIN_HOME?=../dist/kremlin

# Add GF128 tests once code/experimental/gf128 is promoted to code
TARGETS = $(filter-out gf128-%, $(patsubst %.c,%.exe,$(wildcard *.c)))
CFLAGS = -I$(KREMLIN_HOME)/include -I../dist/gcc64-only \
  -I$(KREMLIN_HOME)/kremlib/dist/minimal \
  -I../secure_api/merkle_tree \
  -O3 -march=native -mtune=native

all: $(TARGETS)

test: $(patsubst %.exe,%.test,$(TARGETS))

arm: chacha20-arm-test.exe poly1305-arm-test.exe blake2-arm-test.exe
	./chacha20-arm-test.exe
	./poly1305-arm-test.exe
	./blake2-arm-test.exe

# Dependency

%.d: %.c
	@set -e; rm -f $@; \
	  $(CC) -MM $(CFLAGS) $< > $@.$$$$; \
	  sed 's,\($(notdir $*)\)\.o[ :]*,$(dir $@)\1.o $@ : ,g' < $@.$$$$ > $@; \
	  rm -f $@.$$$$

# Compiling against individual files rather than a whole .a
# Side-effect: running with -B ensures *ALL* files get recompiled with optimized
# flags.

curve64-rfc.exe: $(patsubst %.c,%.o,$(wildcard rfc7748_src/*.c))

%.exe: %.o
	$(CC) $(CFLAGS) $(LDFLAGS) $^ ../dist/gcc64-only/libevercrypt.a -o $@ -lcrypto

chacha20-arm-test.exe: chacha20-arm-test.c
	$(CC) $(CFLAGS) $(LDFLAGS) $^ ../dist/gcc64-only/Hacl_Chacha20.c ../dist/gcc64-only/Hacl_Chacha20_Vec128.c -o $@

poly1305-arm-test.exe: poly1305-arm-test.c
	$(CC) $(CFLAGS) $(LDFLAGS) $^ ../dist/gcc64-only/Hacl_Poly1305_32.c ../dist/gcc64-only/Hacl_Poly1305_128.c -o $@

blake2-arm-test.exe: blake2-arm-test.c
	$(CC) $(CFLAGS) $(LDFLAGS) $^ ../dist/gcc64-only/Hacl_Blake2s_32.c  ../dist/gcc64-only/Hacl_Blake2b_32.c ../dist/gcc64-only/Hacl_Blake2s_128.c -o $@

curve25519-arm-test.exe: curve25519-arm-test.c
	$(CC) $(CFLAGS) $(LDFLAGS) $^ ../dist/gcc64-only/Hacl_Curve25519_51.c -o $@


# Running tests

%.test: %.exe
	./$<
