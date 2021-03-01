# A minimalistic Makefile for all testing options.
# Note: on OSX, this necessitates a recent OpenSSL, possibly installed by brew,
# so I had to do:
# export CFLAGS="-I/usr/local/Cellar/openssl@1.1/1.1.1d/include/"
# export LDFLAGS="-L/usr/local/Cellar/openssl@1.1/1.1.1d/lib"

include ../dist/gcc-compatible/Makefile.config

KREMLIN_HOME?=../dist/kremlin
USER_CFLAGS?=

# Add GF128 tests once code/experimental/gf128 is promoted to code
TARGETS := $(filter-out gf128-%, $(patsubst %.c,%.exe,$(wildcard *.c)))

# Filter the targets if they are not supported
# Vec128
ifneq ($(COMPILE_128),1)
TARGETS := $(filter-out %-128-test-streaming.exe, $(filter-out %-128-test.exe, $(TARGETS)))
endif

# Vec256
ifneq ($(COMPILE_256),1)
TARGETS := $(filter-out %-256-test-streaming.exe, $(filter-out %-256-test.exe, $(TARGETS)))
endif

# Curve64
ifneq ($(COMPILE_COMPILE_INTRINSICS),1)
TARGETS := $(filter-out curve64-%, $(TARGETS))
endif

CFLAGS := -I$(KREMLIN_HOME)/include -I../dist/gcc-compatible \
  -I$(KREMLIN_HOME)/kremlib/dist/minimal \
  -I../secure_api/merkle_tree \
  -O3 $(CFLAGS) $(USER_CFLAGS)

all: $(TARGETS)

test: $(patsubst %.exe,%.test,$(TARGETS))

arm: chacha20-arm-test.test poly1305-arm-test.test blake2-arm-test.test curve25519-arm-test.test

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

# Note that vec-128-test.exe uses lib/c and not dist/gcc-compatible:
# this allows to work on and test the vectorized instructions without
# rebuilding the whole HACL library.
vec-128-test.exe: ../lib/c/libintvector.h vec-128-test.c
	cc -I../lib/c -O3 $(CFLAGS) $(CFLAGS_128) vec-128-test.c -o vec-128-test.exe

../lib/c/libintvector.h:
	touch ../lib/c/libintvector.h

%.exe: %.o
	$(CC) $(CFLAGS) $(LDFLAGS) $^ ../dist/gcc-compatible/libevercrypt.a -o $@ -lcrypto

# Running tests

%.test: %.exe
	./$<

clean:
	rm -f *.exe
