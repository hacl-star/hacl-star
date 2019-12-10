# A minimalistic Makefile for all testing options.

# Add GF128 tests once code/experimental/gf128 is promoted to code
TARGETS = $(filter-out gf128-%, $(patsubst %.c,%.exe,$(wildcard *.c)))

CFLAGS += -I$(KREMLIN_HOME)/include -I../dist/gcc64-only \
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

curve64-rfc.exe: $(patsubst %.c,%.o,$(wildcard rfc7748_src/*.c))

%.exe: %.o
	$(CC) $(CFLAGS) $(LDFLAGS) $^ ../dist/gcc64-only/libevercrypt.a -o $@

# Running tests

%.test: %.exe
	./$<
