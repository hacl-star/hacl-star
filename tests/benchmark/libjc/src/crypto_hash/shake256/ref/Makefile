# -*- Makefile -*-

.PHONY: default clean

default: shake256.japp shake256.s
	@true

clean:
	rm -f shake256.japp shake256.s

%.s: %.japp
	jasminc -lea -pasm $< > $@ || rm -f $@

%.japp: %.jazz
	gpp -I../../../ -o $@ $<
