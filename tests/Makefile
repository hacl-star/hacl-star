# A minimalistic Makefile for all testing options.

TARGETS = $(patsubst %.c,%.exe,$(wildcard *.c))

CFLAGS += -I$(KREMLIN_HOME)/include -I../dist/compact-gcc \
  -I$(KREMLIN_HOME)/kremlib/dist/minimal \
  -O3 -march=native -mtune=native

all: $(TARGETS)

test: $(patsubst %.exe,%.test,$(TARGETS))

# Dependency

%.d: %.c
	@set -e; rm -f $@; \
	  $(CC) -MM $(CFLAGS) $< > $@.$$$$; \
	  sed 's,\($(notdir $*)\)\.o[ :]*,$(dir $@)\1.o $@ : ,g' < $@.$$$$ > $@; \
	  rm -f $@.$$$$

# Compiling against individual files rather than a whole .a
# Side-effect: running with -B ensures *ALL* files get recompiled with optimized
# flags.

%.exe: %.o
	$(CC) $(CFLAGS) $(LDFLAGS) $^ -o $@

curve51-ours.exe curve64-ours.exe: ../dist/compact-gcc/Hacl_Curve25519.o \
  $(KREMLIN_HOME)/kremlib/dist/minimal/FStar_UInt_8_16_32_64.o

curve64-rfc.exe: $(patsubst %.c,%.o,$(wildcard rfc7748_src/*.c))

merkle_tree_test.exe: ../dist/compact-gcc/libevercrypt.a $(KREMLIN_HOME)/kremlib/dist/minimal/libkremlib.a

# Running tests

%.test: %.exe
	./$<
