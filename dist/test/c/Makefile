# Only exercised by Travis CI. This requires a full krmllib to be setup. Regular
# CI regenerates these files and compiles them from the main Makefile. It would
# be nice to delegate building & running C tests to this Makefile from the main
# Makefile for the purposes of sharing.

SOURCES = $(wildcard *.c)
CFLAGS += -I../../gcc-compatible
CFLAGS += -I../../karamel/include
CFLAGS += -I../../karamel/krmllib/dist/minimal

all: $(patsubst %.c,%.test,$(SOURCES))

%.exe: %.o ../../gcc-compatible/libevercrypt.a $(KRML_HOME)/krmllib/dist/generic/libkrmllib.a
	$(CC) $^ -o $@

.PHONY: .test
%.test: %.exe
	./$<

clean:
	rm -rf *.o *.d *.exe
