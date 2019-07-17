# -*- Makefile -*-

.PHONY: default clean

default: sha3224.japp sha3224.s
	@true

clean:
	rm -f sha3224.japp sha3224.s

%.s: %.japp
	jasminc -lea -pasm $< > $@ || rm -f $@

%.japp: %.jazz
	gpp -I../../../ -o $@ $<
