# -*- Makefile -*-

.PHONY: default clean

default: sha3256.japp sha3256.s
	@true

clean:
	rm -f sha3256.japp sha3256.s

%.s: %.japp
	jasminc -lea -pasm $< > $@ || rm -f $@

%.japp: %.jazz
	gpp -I../../../ -o $@ $<
