# TODO: find or write a SCons plugin that uses the jobserver offered
# by GNU Make 4.2 onwards (--jobserver-auth in MAKEFLAGS)

all:
	./run_scons.sh -j 24 --FSTAR-MY-VERSION --FSTAR-EXTRACT --FARGS='$(OTHERFLAGS)' $(VALEFLAGS)

clean:
	./run_scons.sh --clean

.PHONY: all clean
