# -*- Makefile -*-

.PHONY: default clean

default: keccak_1600.japp
	@true

clean:
	rm -f keccak_1600.japp

%.japp: %.jazz
	gpp -I../../../ -o $@ $<
