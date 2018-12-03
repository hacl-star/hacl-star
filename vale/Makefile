# TODO: find or write a SCons plugin that uses the jobserver offered
# by GNU Make 4.2 onwards (--jobserver-auth in MAKEFLAGS)

all:
	./run_scons.sh $$VALE_SCONS_PARALLEL_OPT --FSTAR-MY-VERSION --FARGS='--already_cached "Spec FStar LowStar C"'
	./run_scons.sh $$VALE_SCONS_PARALLEL_OPT --FSTAR-MY-VERSION --FSTAR-EXTRACT --FARGS='--already_cached "Spec FStar LowStar C"'

clean:
	./run_scons.sh --clean

.PHONY: all clean
