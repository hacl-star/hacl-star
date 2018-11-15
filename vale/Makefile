# TODO: find or write a SCons plugin that uses the jobserver offered
# by GNU Make 4.2 onwards (--jobserver-auth in MAKEFLAGS)
#
# For now, the VALE_SCONS_PARALLEL_OPT environment variable (which
# CANNOT be a Make variable) will control the parallel factor for
# SCons tasks.

all:
	# Protect against injection of malicious options
	./run_scons.sh $$VALE_SCONS_PARALLEL_OPT --FSTAR-MY-VERSION
	./run_scons.sh $$VALE_SCONS_PARALLEL_OPT --FSTAR-MY-VERSION --FSTAR-EXTRACT

clean:
	./run_scons.sh --clean

.PHONY: all clean
